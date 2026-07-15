#!/usr/bin/env python
"""Plan, validate, and verify Vera package releases.

The GitHub Actions release workflow deliberately keeps policy in this tested
Python helper instead of embedding it in shell conditionals.  Nothing in this
module uploads files or mutates git state.
"""

from __future__ import annotations

import argparse
from collections.abc import Callable, Sequence
from dataclasses import dataclass
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib
from typing import Any
from urllib.error import HTTPError
from urllib.request import Request, urlopen


ROOT = Path(__file__).resolve().parent.parent
PROJECT = "veralang"
INDEX_JSON_URLS = {
    "pypi": f"https://pypi.org/pypi/{PROJECT}/json",
    "testpypi": f"https://test.pypi.org/pypi/{PROJECT}/json",
}
PACKAGE_AFFECTING_PATHS = ("LICENSE", "PYPI_README.md", "pyproject.toml", "vera")
_VERSION_RE = re.compile(r"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$")


class ReleaseError(ValueError):
    """A release invariant was not satisfied."""


@dataclass(frozen=True)
class ReleasePlan:
    """The result consumed by the release workflow's downstream jobs."""

    publish: bool
    target: str
    version: str


def parse_version(value: str) -> tuple[int, int, int]:
    """Parse Vera's strict ``X.Y.Z`` release format."""
    match = _VERSION_RE.fullmatch(value)
    if match is None:
        raise ReleaseError(f"invalid release version {value!r}; expected X.Y.Z")
    return tuple(int(part) for part in match.groups())  # type: ignore[return-value]


def _project_from_pyproject(text: str, source: str) -> tuple[str, str]:
    try:
        data = tomllib.loads(text)
        name = data["project"]["name"]
        value = data["project"]["version"]
    except (KeyError, TypeError, tomllib.TOMLDecodeError) as exc:
        raise ReleaseError(f"{source}: cannot read project identity: {exc}") from exc
    if not isinstance(name, str) or not isinstance(value, str):
        raise ReleaseError(f"{source}: project name and version must be strings")
    parse_version(value)
    return name, value


def project_version(root: Path = ROOT) -> str:
    """Return the current checkout's project version."""
    path = root / "pyproject.toml"
    name, version = _project_from_pyproject(path.read_text(encoding="utf-8"), str(path))
    if name != PROJECT:
        raise ReleaseError(f"{path}: project name is {name!r}, expected {PROJECT!r}")
    return version


def _git(args: Sequence[str], root: Path = ROOT, *, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if check and result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip()
        raise ReleaseError(f"git {' '.join(args)} failed: {detail}")
    return result.stdout.strip()


def version_at_ref(ref: str, root: Path = ROOT) -> str:
    """Read ``[project].version`` from ``pyproject.toml`` at a git ref."""
    text = _git(["show", f"{ref}:pyproject.toml"], root)
    _name, version = _project_from_pyproject(text, f"{ref}:pyproject.toml")
    return version


def changelog_notes(text: str, version: str) -> str:
    """Extract a non-empty, bullet-bearing release section."""
    parse_version(version)
    heading = re.compile(
        rf"^## \[{re.escape(version)}\](?: - [0-9]{{4}}-[0-9]{{2}}-[0-9]{{2}})?\s*$",
        re.MULTILINE,
    )
    match = heading.search(text)
    if match is None:
        raise ReleaseError(f"CHANGELOG.md has no ## [{version}] release section")
    next_heading = re.search(r"^## \[", text[match.end() :], re.MULTILINE)
    end = match.end() + next_heading.start() if next_heading else len(text)
    notes = text[match.end() : end].strip()
    if not notes or re.search(r"^-\s+\S", notes, re.MULTILINE) is None:
        raise ReleaseError(
            f"CHANGELOG.md section [{version}] must contain at least one bullet"
        )
    return notes


def notes_for_version(version: str, root: Path = ROOT) -> str:
    """Extract release notes from the checkout's changelog."""
    return changelog_notes((root / "CHANGELOG.md").read_text(encoding="utf-8"), version)


def validate_version_sync(root: Path = ROOT) -> None:
    """Run the repository's canonical cross-file version gate."""
    result = subprocess.run(
        [sys.executable, str(root / "scripts" / "check_version_sync.py")],
        cwd=root,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip()
        raise ReleaseError(f"version consistency check failed: {detail}")


def tag_exists(version: str, root: Path = ROOT) -> bool:
    """Return whether the immutable release tag already exists locally."""
    parse_version(version)
    result = subprocess.run(
        ["git", "show-ref", "--verify", "--quiet", f"refs/tags/v{version}"],
        cwd=root,
        check=False,
    )
    return result.returncode == 0


def version_introduction_commit(version: str, root: Path = ROOT) -> str:
    """Find the first-parent commit that introduced ``version`` on main."""
    parse_version(version)
    commits = _git(["rev-list", "--first-parent", "HEAD"], root).splitlines()
    for commit in commits:
        if version_at_ref(commit, root) != version:
            continue
        parents = _git(["rev-list", "--parents", "-n", "1", commit], root).split()
        if len(parents) == 1 or version_at_ref(parents[1], root) != version:
            return commit
    raise ReleaseError(f"cannot find the commit that introduced version {version}")


def package_changes_since(commit: str, root: Path = ROOT) -> list[str]:
    """List changes that would alter package metadata or installed code."""
    output = _git(
        ["diff", "--name-only", f"{commit}..HEAD", "--", *PACKAGE_AFFECTING_PATHS],
        root,
    )
    return output.splitlines() if output else []


def plan_release(
    mode: str,
    *,
    before_ref: str | None = None,
    ref_name: str | None = None,
    confirm_version: str | None = None,
    root: Path = ROOT,
    validate_sync: Callable[[Path], None] = validate_version_sync,
) -> ReleasePlan:
    """Validate an event and return the release workflow plan."""
    current = project_version(root)

    if mode == "push":
        if not before_ref:
            raise ReleaseError("push planning requires --before-ref")
        previous = version_at_ref(before_ref, root)
        if current == previous:
            return ReleasePlan(False, "none", current)
        if parse_version(current) <= parse_version(previous):
            raise ReleaseError(
                f"version must increase on main: {previous} -> {current} is invalid"
            )
        target = "pypi"
    elif mode == "testpypi":
        if confirm_version != current:
            raise ReleaseError(
                f"confirmation {confirm_version!r} does not match version {current}"
            )
        target = "testpypi"
    elif mode == "production-recovery":
        if ref_name != "refs/heads/main":
            raise ReleaseError("production recovery is allowed only from main")
        if confirm_version != current:
            raise ReleaseError(
                f"confirmation {confirm_version!r} does not match version {current}"
            )
        introduced = version_introduction_commit(current, root)
        changes = package_changes_since(introduced, root)
        if changes:
            raise ReleaseError(
                "production recovery is blocked by package-affecting changes after "
                f"the version bump: {', '.join(changes)}"
            )
        target = "pypi"
    else:
        raise ReleaseError(f"unknown release mode {mode!r}")

    validate_sync(root)
    notes_for_version(current, root)
    if target == "pypi" and tag_exists(current, root):
        raise ReleaseError(f"immutable tag v{current} already exists")
    return ReleasePlan(True, target, current)


def distribution_hashes(dist_dir: Path) -> dict[str, str]:
    """Return SHA-256 hashes for exactly one wheel and one sdist."""
    files = sorted(
        path
        for path in dist_dir.iterdir()
        if path.suffix == ".whl" or path.name.endswith(".tar.gz")
    )
    wheels = [path for path in files if path.suffix == ".whl"]
    sdists = [path for path in files if path.name.endswith(".tar.gz")]
    if len(wheels) != 1 or len(sdists) != 1 or len(files) != 2:
        raise ReleaseError(
            f"{dist_dir}: expected exactly one wheel and one sdist; "
            f"found {[path.name for path in files]}"
        )
    return {path.name: sha256(path.read_bytes()).hexdigest() for path in files}


def write_manifest(dist_dir: Path, output: Path) -> None:
    """Write a deterministic SHA-256 manifest for the release archives."""
    hashes = distribution_hashes(dist_dir)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        "".join(f"{digest}  {name}\n" for name, digest in sorted(hashes.items())),
        encoding="utf-8",
    )


def _fetch_registry(index: str) -> dict[str, Any] | None:
    url = INDEX_JSON_URLS[index]
    request = Request(url, headers={"User-Agent": "vera-release-verifier/1"})
    try:
        with urlopen(request, timeout=30) as response:  # noqa: S310 - fixed URLs
            data = json.load(response)
    except HTTPError as exc:
        if exc.code == 404:
            return None
        raise ReleaseError(f"{index} returned HTTP {exc.code}") from exc
    if not isinstance(data, dict):
        raise ReleaseError(f"{index} returned a non-object JSON response")
    return data


def registry_version_files(
    index: str,
    version: str,
    *,
    fetch: Callable[[str], dict[str, Any] | None] = _fetch_registry,
) -> dict[str, str] | None:
    """Return registry filename-to-SHA mappings, or ``None`` if absent."""
    if index not in INDEX_JSON_URLS:
        raise ReleaseError(f"unknown package index {index!r}")
    parse_version(version)
    payload = fetch(index)
    if payload is None:
        return None
    releases = payload.get("releases")
    if not isinstance(releases, dict):
        raise ReleaseError(f"{index} JSON has no releases object")
    files = releases.get(version)
    if not files:
        return None
    result: dict[str, str] = {}
    for item in files:
        if not isinstance(item, dict):
            raise ReleaseError(f"{index} release {version} has malformed file data")
        filename = item.get("filename")
        digests = item.get("digests")
        digest = digests.get("sha256") if isinstance(digests, dict) else None
        if not isinstance(filename, str) or not isinstance(digest, str):
            raise ReleaseError(f"{index} release {version} lacks filename/SHA-256 data")
        result[filename] = digest
    return result


def assert_version_absent(
    index: str,
    version: str,
    *,
    fetch: Callable[[str], dict[str, Any] | None] = _fetch_registry,
) -> None:
    """Fail rather than overwriting or silently skipping an immutable version."""
    if registry_version_files(index, version, fetch=fetch) is not None:
        raise ReleaseError(f"{PROJECT} {version} already exists on {index}")


def verify_registry(
    index: str,
    version: str,
    dist_dir: Path,
    *,
    attempts: int = 12,
    delay: float = 5.0,
    fetch: Callable[[str], dict[str, Any] | None] = _fetch_registry,
    sleep: Callable[[float], None] = time.sleep,
) -> None:
    """Verify registry filenames and hashes, retrying index propagation."""
    expected = distribution_hashes(dist_dir)
    actual: dict[str, str] | None = None
    for attempt in range(1, attempts + 1):
        actual = registry_version_files(index, version, fetch=fetch)
        if actual == expected:
            break
        if attempt < attempts:
            sleep(delay)
    if actual is None:
        raise ReleaseError(f"{PROJECT} {version} did not appear on {index}")
    if set(actual) != set(expected):
        raise ReleaseError(
            f"{index} filenames differ: expected {sorted(expected)}, got {sorted(actual)}"
        )
    mismatches = [
        name for name, digest in expected.items() if actual.get(name) != digest
    ]
    if mismatches:
        raise ReleaseError(f"{index} SHA-256 mismatch for: {', '.join(mismatches)}")


def _write_github_outputs(path: Path, plan: ReleasePlan) -> None:
    with path.open("a", encoding="utf-8") as output:
        output.write(f"publish={'true' if plan.publish else 'false'}\n")
        output.write(f"target={plan.target}\n")
        output.write(f"version={plan.version}\n")
        output.write(f"artifact={PROJECT}-{plan.version}\n")


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)

    prepare = commands.add_parser("prepare", help="validate and plan a release event")
    prepare.add_argument(
        "--mode", choices=("push", "testpypi", "production-recovery"), required=True
    )
    prepare.add_argument("--before-ref")
    prepare.add_argument("--ref-name")
    prepare.add_argument("--confirm-version")
    prepare.add_argument("--github-output", type=Path, required=True)

    notes = commands.add_parser("notes", help="extract a changelog release section")
    notes.add_argument("--version", required=True)
    notes.add_argument("--output", type=Path, required=True)

    manifest = commands.add_parser("manifest", help="write archive SHA-256 values")
    manifest.add_argument("--dist-dir", type=Path, default=Path("dist"))
    manifest.add_argument("--output", type=Path, required=True)

    absent = commands.add_parser("assert-absent", help="require an unpublished version")
    absent.add_argument("--index", choices=tuple(INDEX_JSON_URLS), required=True)
    absent.add_argument("--version", required=True)

    verify = commands.add_parser("verify-registry", help="verify uploaded archives")
    verify.add_argument("--index", choices=tuple(INDEX_JSON_URLS), required=True)
    verify.add_argument("--version", required=True)
    verify.add_argument("--dist-dir", type=Path, default=Path("dist"))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command == "prepare":
            plan = plan_release(
                args.mode,
                before_ref=args.before_ref,
                ref_name=args.ref_name,
                confirm_version=args.confirm_version,
            )
            _write_github_outputs(args.github_output, plan)
            action = f"publish to {plan.target}" if plan.publish else "no release"
            print(f"Release plan for {plan.version}: {action}.")
        elif args.command == "notes":
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(
                notes_for_version(args.version) + "\n", encoding="utf-8"
            )
        elif args.command == "manifest":
            write_manifest(args.dist_dir, args.output)
        elif args.command == "assert-absent":
            assert_version_absent(args.index, args.version)
            print(f"{PROJECT} {args.version} is absent from {args.index}.")
        elif args.command == "verify-registry":
            verify_registry(args.index, args.version, args.dist_dir)
            print(
                f"{PROJECT} {args.version} filenames and SHA-256 hashes match on "
                f"{args.index}."
            )
    except (OSError, ReleaseError, subprocess.SubprocessError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
