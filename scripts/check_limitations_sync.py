#!/usr/bin/env python
"""Verify limitation tracking is consistent across documentation tiers.

Vera documents limitations in five places:
  1. KNOWN_ISSUES.md — user-facing "Bugs" and "Limitations" tables (canonical)
  2. vera/README.md — contributor-facing "Current Limitations" table
  3. spec/ chapters — language-design-level limitation tables (ch 8, 9, 11, 12)
  4. SKILL.md — agent-facing "Known Limitations" and "Known Bugs" tables
  5. LSP_SERVER.md — language-server "Current limitations" table

This script extracts GitHub issue numbers from each tier and checks:
  - Every limitation issue in tiers 2–5 appears in KNOWN_ISSUES.md
  - No stale "Done" entries remain in limitation tables
  - Every section this script is configured to read actually exists
    (a renamed or deleted heading fails loudly instead of silently
    shrinking the check's coverage)

With --check-states, also verifies via GitHub API that no closed issues are
listed as open limitations (slower — one API call per issue).

Fast enough for a pre-commit hook in default mode.
"""

import re
import subprocess
import sys
from pathlib import Path


_ISSUE_LINK_RE = re.compile(r"\[#(\d+)\]\(https://github\.com/[^)]+\)")


def _row_issue_links(line: str, issue_column_only: bool) -> set[int]:
    """Issue links in one Markdown table row.

    ``issue_column_only`` narrows the scan to the row's LAST cell — the
    **Issue** column every limitation and bug table carries.  The two
    widths answer different questions and both are wanted (#1337).

    The presence checks want the WIDE form: an issue named anywhere in a
    row is tracked by that row, so a cross-reference still counts as
    coverage.  The ``--check-states`` scan wants the NARROW form,
    because a row's prose legitimately cites CLOSED issues for context
    — "the general disease behind [#1315]", "fixed in [#1305]" — and
    reading those as claims that the issue is still open failed the
    nightly on eight such citations while the row's own Issue column was
    correct throughout.
    """
    source = line.strip().strip("|").split("|")[-1] if issue_column_only else line
    return {int(n) for n in _ISSUE_LINK_RE.findall(source)}


def extract_limitation_table_issues(
    text: str, table_header: str, issue_column_only: bool = False
) -> set[int]:
    """Extract issue numbers from a Markdown limitation table.

    Finds the table that follows `table_header` and extracts all issue
    references from it.  Stops at the next heading or blank line after
    the table.
    """
    issues: set[int] = set()
    in_table = False
    header_found = False

    for line in text.splitlines():
        # Look for the section heading
        if table_header in line:
            header_found = True
            continue
        if not header_found:
            continue

        # Skip blank lines between heading and table
        if not in_table and line.strip() == "":
            continue

        # Table rows start with |
        if line.strip().startswith("|"):
            in_table = True
            # Skip separator rows
            if re.match(r"^\|[\s\-|]+\|$", line.strip()):
                continue
            # Extract issue numbers from this row
            issues.update(_row_issue_links(line, issue_column_only))
        elif in_table:
            # Table ended
            break

    return issues


def extract_section_issues(
    text: str, heading: str, issue_column_only: bool = False
) -> set[int] | None:
    """Extract issue links from the table rows of one `## heading` section.

    The scan is bounded at the next `## ` heading (or end of file), and
    only lines that are Markdown table rows contribute — issue links in
    surrounding prose are narrative, not inventory.  Returns ``None``
    when the heading is absent so the caller can treat a renamed or
    deleted section as an error rather than an empty result.
    """
    m = re.search(
        rf"^## {re.escape(heading)}\s*$\n(.*?)(?=^## |\Z)",
        text,
        re.DOTALL | re.MULTILINE,
    )
    if not m:
        return None
    issues: set[int] = set()
    for line in m.group(1).splitlines():
        if not line.strip().startswith("|"):
            continue
        issues.update(_row_issue_links(line, issue_column_only))
    return issues


def extract_done_and_open(
    text: str, issue_column_only: bool = False
) -> tuple[set[int], set[int]]:
    """Extract open and Done issue sets from vera/README limitation table.

    Scans all table rows in the Current Limitations section.  Rows
    containing "Done" go into the done set; others go into the open set.
    """
    open_issues: set[int] = set()
    done_issues: set[int] = set()
    in_section = False

    for line in text.splitlines():
        if "## Current Limitations" in line:
            in_section = True
            continue
        if not in_section:
            continue
        # Stop at next section
        if line.startswith("## ") and "Current Limitations" not in line:
            break
        if not line.strip().startswith("|") or "---" in line:
            continue
        row_issues = _row_issue_links(line, issue_column_only)
        if "Done" in line:
            done_issues.update(row_issues)
        else:
            open_issues.update(row_issues)

    return open_issues, done_issues


def check_issue_states(issue_numbers: set[int]) -> dict[int, str]:
    """Check open/closed state of GitHub issues using gh CLI."""
    if not issue_numbers:
        return {}

    states: dict[int, str] = {}
    for num in sorted(issue_numbers):
        try:
            result = subprocess.run(
                [
                    "gh", "issue", "view", str(num),
                    "--json", "state", "-q", ".state",
                ],
                capture_output=True,
                text=True,
                encoding="utf-8",
                timeout=10,
                check=False,
            )
            if result.returncode == 0:
                states[num] = result.stdout.strip()
            else:
                states[num] = "UNKNOWN"
        except (subprocess.TimeoutExpired, FileNotFoundError):
            states[num] = "UNKNOWN"

    return states


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    errors: list[str] = []

    do_check_states = "--check-states" in sys.argv

    # ------------------------------------------------------------------
    # 1. Extract limitation issues from each documentation tier
    # ------------------------------------------------------------------

    # Tier 1: KNOWN_ISSUES.md — user-facing limitations and bugs tables
    readme_text = (root / "KNOWN_ISSUES.md").read_text(encoding="utf-8")
    readme_issues = extract_limitation_table_issues(
        readme_text, "## Limitations"
    )
    readme_bugs = extract_limitation_table_issues(
        readme_text, "## Bugs"
    )
    readme_issues |= readme_bugs  # issues in either table count as tracked

    # Tier 2: vera/README.md — contributor-facing limitations table
    vera_readme_text = (root / "vera/README.md").read_text(encoding="utf-8")
    vera_readme_open, vera_readme_done = extract_done_and_open(vera_readme_text)

    # Tier 3: Spec chapters with limitation sections
    spec_issues: dict[str, set[int]] = {}
    spec_files = [
        ("spec/08-modules.md", "## 8.11 Limitations"),
        ("spec/09-standard-library.md", "## 9.9 Limitations"),
        ("spec/11-compilation.md", "## 11.17 Limitations"),
        ("spec/12-runtime.md", "## 12.8 Limitations"),
    ]
    for spec_path, heading in spec_files:
        full_path = root / spec_path
        if not full_path.exists():
            errors.append(
                f"{spec_path}: file not found (listed in"
                f" check_limitations_sync.py)"
            )
            continue
        text = full_path.read_text(encoding="utf-8")
        if heading.split("## ")[1] not in text:
            errors.append(
                f"{spec_path}: expected '{heading}' section not found"
                f" (listed in check_limitations_sync.py)"
            )
            continue
        issues = extract_limitation_table_issues(text, heading)
        if issues:
            spec_issues[spec_path] = issues

    all_spec_issues: set[int] = set()
    for issues in spec_issues.values():
        all_spec_issues |= issues

    # Tier 4: SKILL.md — agent-facing limitations and bugs tables
    skill_text = (root / "SKILL.md").read_text(encoding="utf-8")
    skill_issues: set[int] = set()
    for heading_text in ("Known Limitations", "Known Bugs and Workarounds"):
        found = extract_section_issues(skill_text, heading_text)
        if found is None:
            errors.append(
                f"SKILL.md: expected '## {heading_text}' section not found"
                f" (listed in check_limitations_sync.py)"
            )
        else:
            skill_issues |= found

    # Tier 5: LSP_SERVER.md — language-server limitations table
    lsp_text = (root / "LSP_SERVER.md").read_text(encoding="utf-8")
    lsp_found = extract_section_issues(lsp_text, "Current limitations")
    if lsp_found is None:
        errors.append(
            "LSP_SERVER.md: expected '## Current limitations' section not"
            " found (listed in check_limitations_sync.py)"
        )
        lsp_issues: set[int] = set()
    else:
        lsp_issues = lsp_found

    # ------------------------------------------------------------------
    # 2. Cross-check: every open limitation should appear in README.md
    # ------------------------------------------------------------------

    all_documented_open = (
        vera_readme_open | all_spec_issues | skill_issues | lsp_issues
    )
    missing_from_readme = all_documented_open - readme_issues
    for num in sorted(missing_from_readme):
        sources = []
        if num in vera_readme_open:
            sources.append("vera/README.md")
        for spec_path, issues in spec_issues.items():
            if num in issues:
                sources.append(spec_path)
        if num in skill_issues:
            sources.append("SKILL.md")
        if num in lsp_issues:
            sources.append("LSP_SERVER.md")
        errors.append(
            f"Issue #{num} appears in {', '.join(sources)} "
            f"but is missing from KNOWN_ISSUES.md"
        )

    # ------------------------------------------------------------------
    # 3. Check for stale "Done" entries
    # ------------------------------------------------------------------

    if vera_readme_done:
        errors.append(
            f"vera/README.md still has {len(vera_readme_done)} 'Done' "
            f"limitation(s) that should be removed: "
            f"{', '.join(f'#{n}' for n in sorted(vera_readme_done))}"
        )

    # ------------------------------------------------------------------
    # 4. (Optional) Check for closed issues via GitHub API
    # ------------------------------------------------------------------

    if do_check_states:
        # #1337: the state scan is an INVENTORY question — "does this table
        # still claim the issue is open?" — so it reads each row's Issue
        # column, not the row's prose.  The presence checks above keep the
        # wide reading; re-extracting here is what keeps the two apart.
        st_readme = extract_limitation_table_issues(
            readme_text, "## Limitations", issue_column_only=True
        ) | extract_limitation_table_issues(
            readme_text, "## Bugs", issue_column_only=True
        )
        st_vera_readme_open, _st_done = extract_done_and_open(
            vera_readme_text, issue_column_only=True
        )
        st_spec_issues: dict[str, set[int]] = {}
        for spec_path, heading in spec_files:
            full_path = root / spec_path
            if not full_path.exists():
                continue
            found_spec = extract_limitation_table_issues(
                full_path.read_text(encoding="utf-8"),
                heading,
                issue_column_only=True,
            )
            if found_spec:
                st_spec_issues[spec_path] = found_spec
        st_skill: set[int] = set()
        for heading_text in ("Known Limitations", "Known Bugs and Workarounds"):
            found_skill = extract_section_issues(
                skill_text, heading_text, issue_column_only=True
            )
            if found_skill:
                st_skill |= found_skill
        st_lsp = extract_section_issues(
            lsp_text, "Current limitations", issue_column_only=True
        ) or set()

        all_issues = (
            st_readme
            | st_vera_readme_open
            | {n for s in st_spec_issues.values() for n in s}
            | st_skill
            | st_lsp
        )
        if all_issues:
            states = check_issue_states(all_issues)
            for num in sorted(all_issues):
                state = states.get(num, "UNKNOWN")
                if state == "CLOSED":
                    locations = []
                    if num in st_readme:
                        locations.append("KNOWN_ISSUES.md")
                    if num in st_vera_readme_open:
                        locations.append("vera/README.md")
                    for spec_path, issues in st_spec_issues.items():
                        if num in issues:
                            locations.append(spec_path)
                    if num in st_skill:
                        locations.append("SKILL.md")
                    if num in st_lsp:
                        locations.append("LSP_SERVER.md")
                    errors.append(
                        f"Issue #{num} is CLOSED but still listed as "
                        f"open limitation in: {', '.join(locations)}"
                    )
                elif state == "UNKNOWN":
                    # A state that cannot be determined (gh CLI missing,
                    # auth failure, rate limit, timeout) must be loud: a
                    # silent pass here would leave the scheduled #852
                    # workflow green while checking nothing.
                    errors.append(
                        f"Issue #{num} state could not be determined "
                        "(gh CLI missing, auth failure, or timeout); "
                        "--check-states cannot verify the limitation tables"
                    )

    # ------------------------------------------------------------------
    # 5. Report
    # ------------------------------------------------------------------

    if errors:
        print(
            f"ERROR: {len(errors)} limitation sync issue(s):",
            file=sys.stderr,
        )
        for err in errors:
            print(f"  {err}", file=sys.stderr)
        return 1

    mode = " (with state check)" if do_check_states else ""
    print(
        f"Limitation tracking is consistent{mode} "
        f"({len(readme_issues)} in KNOWN_ISSUES.md, "
        f"{len(vera_readme_open)} in vera/README.md, "
        f"{len(all_spec_issues)} across spec chapters, "
        f"{len(skill_issues)} in SKILL.md, "
        f"{len(lsp_issues)} in LSP_SERVER.md)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
