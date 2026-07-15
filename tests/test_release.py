"""Release-policy tests for ``scripts/release.py`` (#481)."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import subprocess
import sys
from typing import Any

import pytest


_SCRIPT = Path(__file__).parent.parent / "scripts" / "release.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("release_helper", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


release = _load()


def _root(tmp_path: Path, version: str = "0.1.5") -> Path:
    (tmp_path / "pyproject.toml").write_text(
        f'[project]\nname = "veralang"\nversion = "{version}"\n',
        encoding="utf-8",
    )
    (tmp_path / "CHANGELOG.md").write_text(
        f"# Changelog\n\n## [{version}] - 2026-07-15\n\n"
        "### Added\n\n- Release machinery.\n\n"
        "## [0.1.4] - 2026-06-01\n\n- Previous.\n",
        encoding="utf-8",
    )
    return tmp_path


def _dist(tmp_path: Path) -> Path:
    dist = tmp_path / "dist"
    dist.mkdir()
    (dist / "veralang-0.1.5-py3-none-any.whl").write_bytes(b"wheel")
    (dist / "veralang-0.1.5.tar.gz").write_bytes(b"sdist")
    return dist


def _git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=True,
    )
    return result.stdout.strip()


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(root, "commit", "-m", message)
    return _git(root, "rev-parse", "HEAD")


class TestVersions:
    @pytest.mark.parametrize(
        ("value", "expected"),
        [("0.1.5", (0, 1, 5)), ("12.34.56", (12, 34, 56))],
    )
    def test_parse(self, value: str, expected: tuple[int, int, int]) -> None:
        assert release.parse_version(value) == expected

    @pytest.mark.parametrize(
        "value", ["v0.1.5", "0.1", "0.1.5rc1", "01.2.3", "1.02.3", ""]
    )
    def test_rejects_non_release_versions(self, value: str) -> None:
        with pytest.raises(release.ReleaseError, match="expected X.Y.Z"):
            release.parse_version(value)

    def test_project_version(self, tmp_path: Path) -> None:
        assert release.project_version(_root(tmp_path)) == "0.1.5"

    def test_project_name_must_be_veralang(self, tmp_path: Path) -> None:
        root = _root(tmp_path)
        (root / "pyproject.toml").write_text(
            '[project]\nname = "vera"\nversion = "0.1.5"\n', encoding="utf-8"
        )
        with pytest.raises(release.ReleaseError, match="expected 'veralang'"):
            release.project_version(root)


class TestChangelogNotes:
    def test_extracts_matching_section(self) -> None:
        text = (
            "## [Unreleased]\n\n- Future.\n\n"
            "## [0.1.5] - 2026-07-15\n\n### Fixed\n\n- One.\n- Two.\n\n"
            "## [0.1.4] - 2026-07-01\n\n- Old.\n"
        )
        assert release.changelog_notes(text, "0.1.5") == "### Fixed\n\n- One.\n- Two."

    def test_date_is_optional(self) -> None:
        assert (
            release.changelog_notes("## [0.1.5]\n\n- Notes.\n", "0.1.5") == "- Notes."
        )

    def test_missing_section_fails(self) -> None:
        with pytest.raises(release.ReleaseError, match="no ## \\[0.1.5\\]"):
            release.changelog_notes("## [0.1.4]\n\n- Old.\n", "0.1.5")

    @pytest.mark.parametrize(
        "body", ["", "\n### Added\n", "\nSome prose but no release bullet.\n"]
    )
    def test_section_requires_a_bullet(self, body: str) -> None:
        with pytest.raises(release.ReleaseError, match="at least one bullet"):
            release.changelog_notes(f"## [0.1.5]{body}", "0.1.5")


class TestPlanning:
    def test_recovery_tracks_first_parent_bump_and_package_changes(
        self, tmp_path: Path
    ) -> None:
        root = _root(tmp_path, "0.1.4")
        (root / "vera").mkdir()
        (root / "vera" / "cli.py").write_text("OLD = True\n", encoding="utf-8")
        _git(root, "init", "-b", "main")
        _git(root, "config", "user.email", "release-test@example.invalid")
        _git(root, "config", "user.name", "Release Test")
        _commit(root, "initial")

        (root / "pyproject.toml").write_text(
            '[project]\nname = "veralang"\nversion = "0.1.5"\n',
            encoding="utf-8",
        )
        introduced = _commit(root, "bump version")
        (root / "README.md").write_text("Docs only.\n", encoding="utf-8")
        _commit(root, "docs after bump")

        assert release.version_introduction_commit("0.1.5", root) == introduced
        assert release.package_changes_since(introduced, root) == []

        (root / "vera" / "cli.py").write_text("NEW = True\n", encoding="utf-8")
        _commit(root, "package change")
        assert release.package_changes_since(introduced, root) == ["vera/cli.py"]

    def test_non_version_push_is_noop(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        root = _root(tmp_path)
        monkeypatch.setattr(release, "version_at_ref", lambda _ref, _root: "0.1.5")
        plan = release.plan_release(
            "push",
            before_ref="before",
            root=root,
            validate_sync=lambda _root: pytest.fail("must not validate a no-op"),
        )
        assert plan == release.ReleasePlan(False, "none", "0.1.5")

    def test_increasing_push_plans_production(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        root = _root(tmp_path)
        monkeypatch.setattr(release, "version_at_ref", lambda _ref, _root: "0.1.4")
        monkeypatch.setattr(release, "tag_exists", lambda _version, _root: False)
        plan = release.plan_release(
            "push", before_ref="before", root=root, validate_sync=lambda _root: None
        )
        assert plan == release.ReleasePlan(True, "pypi", "0.1.5")

    def test_decrease_is_rejected(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        root = _root(tmp_path, "0.1.4")
        monkeypatch.setattr(release, "version_at_ref", lambda _ref, _root: "0.1.5")
        with pytest.raises(release.ReleaseError, match="must increase"):
            release.plan_release(
                "push", before_ref="before", root=root, validate_sync=lambda _root: None
            )

    def test_push_requires_before_ref(self, tmp_path: Path) -> None:
        with pytest.raises(release.ReleaseError, match="requires --before-ref"):
            release.plan_release("push", root=_root(tmp_path))

    def test_testpypi_requires_exact_confirmation(self, tmp_path: Path) -> None:
        with pytest.raises(release.ReleaseError, match="does not match"):
            release.plan_release(
                "testpypi",
                confirm_version="0.1.4",
                root=_root(tmp_path),
                validate_sync=lambda _root: None,
            )

    def test_testpypi_allows_an_existing_production_tag(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setattr(release, "tag_exists", lambda _version, _root: True)
        plan = release.plan_release(
            "testpypi",
            confirm_version="0.1.5",
            root=_root(tmp_path),
            validate_sync=lambda _root: None,
        )
        assert plan.target == "testpypi"

    def test_production_recovery_requires_main(self, tmp_path: Path) -> None:
        with pytest.raises(release.ReleaseError, match="only from main"):
            release.plan_release(
                "production-recovery",
                ref_name="refs/heads/release/0.1.5",
                confirm_version="0.1.5",
                root=_root(tmp_path),
                validate_sync=lambda _root: None,
            )

    def test_production_recovery_rejects_later_package_changes(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setattr(
            release, "version_introduction_commit", lambda _version, _root: "abc"
        )
        monkeypatch.setattr(
            release, "package_changes_since", lambda _commit, _root: ["vera/cli.py"]
        )
        with pytest.raises(release.ReleaseError, match="vera/cli.py"):
            release.plan_release(
                "production-recovery",
                ref_name="refs/heads/main",
                confirm_version="0.1.5",
                root=_root(tmp_path),
                validate_sync=lambda _root: None,
            )

    def test_production_recovery_without_changes_is_allowed(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setattr(
            release, "version_introduction_commit", lambda _version, _root: "abc"
        )
        monkeypatch.setattr(release, "package_changes_since", lambda _commit, _root: [])
        monkeypatch.setattr(release, "tag_exists", lambda _version, _root: False)
        plan = release.plan_release(
            "production-recovery",
            ref_name="refs/heads/main",
            confirm_version="0.1.5",
            root=_root(tmp_path),
            validate_sync=lambda _root: None,
        )
        assert plan.target == "pypi"

    def test_production_rejects_existing_immutable_tag(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setattr(release, "version_at_ref", lambda _ref, _root: "0.1.4")
        monkeypatch.setattr(release, "tag_exists", lambda _version, _root: True)
        with pytest.raises(release.ReleaseError, match="already exists"):
            release.plan_release(
                "push",
                before_ref="before",
                root=_root(tmp_path),
                validate_sync=lambda _root: None,
            )


class TestArchivesAndRegistry:
    def test_distribution_hashes_and_manifest(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)
        assert set(hashes) == {
            "veralang-0.1.5-py3-none-any.whl",
            "veralang-0.1.5.tar.gz",
        }
        output = tmp_path / "release" / "SHA256SUMS"
        release.write_manifest(dist, output)
        assert output.read_text(encoding="utf-8").splitlines() == [
            f"{hashes[name]}  {name}" for name in sorted(hashes)
        ]

    def test_requires_exactly_one_wheel_and_sdist(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        (dist / "another.whl").write_bytes(b"extra")
        with pytest.raises(release.ReleaseError, match="exactly one"):
            release.distribution_hashes(dist)

    def test_registry_version_files(self) -> None:
        payload = {
            "releases": {
                "0.1.5": [
                    {"filename": "a.whl", "digests": {"sha256": "abc"}},
                    {"filename": "a.tar.gz", "digests": {"sha256": "def"}},
                ]
            }
        }
        assert release.registry_version_files(
            "pypi", "0.1.5", fetch=lambda _index: payload
        ) == {"a.whl": "abc", "a.tar.gz": "def"}

    def test_absent_project_or_version_returns_none(self) -> None:
        assert (
            release.registry_version_files("pypi", "0.1.5", fetch=lambda _index: None)
            is None
        )
        assert (
            release.registry_version_files(
                "pypi", "0.1.5", fetch=lambda _index: {"releases": {}}
            )
            is None
        )

    @pytest.mark.parametrize(
        ("payload", "message"),
        [
            ({"releases": []}, "no releases object"),
            ({"releases": {"0.1.5": ["bad"]}}, "malformed file data"),
            (
                {"releases": {"0.1.5": [{"digests": {"sha256": "abc"}}]}},
                "lacks filename/SHA-256 data",
            ),
            (
                {"releases": {"0.1.5": [{"filename": "a.whl"}]}},
                "lacks filename/SHA-256 data",
            ),
        ],
    )
    def test_registry_rejects_malformed_payloads(
        self, payload: dict[str, Any], message: str
    ) -> None:
        with pytest.raises(release.ReleaseError, match=message):
            release.registry_version_files(
                "pypi", "0.1.5", fetch=lambda _index: payload
            )

    def test_assert_absent_rejects_existing_version(self) -> None:
        payload = {
            "releases": {"0.1.5": [{"filename": "a", "digests": {"sha256": "b"}}]}
        }
        with pytest.raises(release.ReleaseError, match="already exists"):
            release.assert_version_absent("pypi", "0.1.5", fetch=lambda _index: payload)

    def test_verify_registry_matches_exact_files_and_hashes(
        self, tmp_path: Path
    ) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)
        payload = {
            "releases": {
                "0.1.5": [
                    {"filename": name, "digests": {"sha256": digest}}
                    for name, digest in hashes.items()
                ]
            }
        }
        release.verify_registry(
            "pypi", "0.1.5", dist, attempts=1, fetch=lambda _index: payload
        )

    def test_verify_registry_retries_propagation(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)
        payload = {
            "releases": {
                "0.1.5": [
                    {"filename": name, "digests": {"sha256": digest}}
                    for name, digest in hashes.items()
                ]
            }
        }
        responses = iter([None, payload])
        sleeps: list[float] = []
        release.verify_registry(
            "testpypi",
            "0.1.5",
            dist,
            attempts=2,
            delay=0.25,
            fetch=lambda _index: next(responses),
            sleep=sleeps.append,
        )
        assert sleeps == [0.25]

    def test_verify_registry_retries_stale_hashes(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)

        def payload(digests: dict[str, str]) -> dict[str, Any]:
            return {
                "releases": {
                    "0.1.5": [
                        {"filename": name, "digests": {"sha256": digest}}
                        for name, digest in digests.items()
                    ]
                }
            }

        responses = iter([payload(dict.fromkeys(hashes, "0" * 64)), payload(hashes)])
        sleeps: list[float] = []
        release.verify_registry(
            "pypi",
            "0.1.5",
            dist,
            attempts=2,
            delay=0.25,
            fetch=lambda _index: next(responses),
            sleep=sleeps.append,
        )
        assert sleeps == [0.25]

    def test_verify_registry_rejects_hash_mismatch(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)
        payload = {
            "releases": {
                "0.1.5": [
                    {"filename": name, "digests": {"sha256": "0" * 64}}
                    for name in hashes
                ]
            }
        }
        with pytest.raises(release.ReleaseError, match="SHA-256 mismatch"):
            release.verify_registry(
                "pypi", "0.1.5", dist, attempts=1, fetch=lambda _index: payload
            )

    def test_verify_registry_rejects_extra_filename(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)
        files = [
            {"filename": name, "digests": {"sha256": digest}}
            for name, digest in hashes.items()
        ]
        files.append({"filename": "unexpected.zip", "digests": {"sha256": "x"}})
        payload = {"releases": {"0.1.5": files}}
        with pytest.raises(release.ReleaseError, match="filenames differ"):
            release.verify_registry(
                "pypi", "0.1.5", dist, attempts=1, fetch=lambda _index: payload
            )


class TestCLI:
    def test_write_github_outputs(self, tmp_path: Path) -> None:
        output = tmp_path / "github-output"
        release._write_github_outputs(
            output, release.ReleasePlan(False, "none", "0.1.5")
        )
        assert output.read_text(encoding="utf-8").splitlines() == [
            "publish=false",
            "target=none",
            "version=0.1.5",
            "artifact=veralang-0.1.5",
        ]

    def test_main_prepare_writes_github_outputs(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        def plan(mode: str, **kwargs: Any) -> Any:
            assert mode == "push"
            assert kwargs["before_ref"] == "before"
            return release.ReleasePlan(True, "pypi", "0.1.5")

        monkeypatch.setattr(release, "plan_release", plan)
        output = tmp_path / "github-output"
        assert (
            release.main(
                [
                    "prepare",
                    "--mode",
                    "push",
                    "--before-ref",
                    "before",
                    "--github-output",
                    str(output),
                ]
            )
            == 0
        )
        assert output.read_text(encoding="utf-8").splitlines() == [
            "publish=true",
            "target=pypi",
            "version=0.1.5",
            "artifact=veralang-0.1.5",
        ]

    def test_main_notes(self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(
            release, "notes_for_version", lambda version: f"- Notes for {version}."
        )
        output = tmp_path / "release" / "notes.md"
        assert (
            release.main(["notes", "--version", "0.1.5", "--output", str(output)]) == 0
        )
        assert output.read_text(encoding="utf-8") == "- Notes for 0.1.5.\n"

    def test_main_manifest(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        output = tmp_path / "release" / "SHA256SUMS"
        assert (
            release.main(["manifest", "--dist-dir", str(dist), "--output", str(output)])
            == 0
        )
        assert output.read_text(encoding="utf-8").splitlines() == [
            f"{digest}  {name}"
            for name, digest in sorted(release.distribution_hashes(dist).items())
        ]

    def test_main_assert_absent(self, monkeypatch: pytest.MonkeyPatch) -> None:
        calls: list[tuple[str, str]] = []
        monkeypatch.setattr(
            release,
            "assert_version_absent",
            lambda index, version: calls.append((index, version)),
        )
        assert (
            release.main(["assert-absent", "--index", "testpypi", "--version", "0.1.5"])
            == 0
        )
        assert calls == [("testpypi", "0.1.5")]

    def test_main_verify_registry(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        calls: list[tuple[str, str, Path]] = []
        monkeypatch.setattr(
            release,
            "verify_registry",
            lambda index, version, dist: calls.append((index, version, dist)),
        )
        dist = tmp_path / "dist"
        assert (
            release.main(
                [
                    "verify-registry",
                    "--index",
                    "pypi",
                    "--version",
                    "0.1.5",
                    "--dist-dir",
                    str(dist),
                ]
            )
            == 0
        )
        assert calls == [("pypi", "0.1.5", dist)]
