#!/usr/bin/env python3
"""Audit structural coverage of manuscript chapters by Lean modules.

A module's existence or successful compilation does NOT prove the entire chapter.
This audit is non-blocking by default; --strict fails when coverage is incomplete.
"""

from __future__ import annotations

import argparse
import os
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHAPTER_LINK = re.compile(
    r"^-\s*\[Chapter\s+(\d+)\b[^\]]*\]\(([^)]+\.md)\)\s*$",
    flags=re.MULTILINE,
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--strict",
        action="store_true",
        help="fail when a manuscript chapter has no source module or root import",
    )
    args = parser.parse_args()

    summary_file = ROOT / "manuscript" / "SUMMARY.md"
    book_file = ROOT / "Book.lean"
    chapters = [(int(n), relative) for n, relative in CHAPTER_LINK.findall(
        summary_file.read_text(encoding="utf-8")
    )]
    if not chapters:
        raise SystemExit("ERROR: Found no chapter links in manuscript/SUMMARY.md")

    root_imports = set(re.findall(
        r"(?m)^\s*(?:public\s+)?import\s+(Book\.Chapters\.Chapter\d+)\s*$",
        book_file.read_text(encoding="utf-8"),
    ))
    missing_manuscript = []
    missing_modules = []
    missing_imports = []
    covered = []
    for number, relative in chapters:
        chapter = ROOT / "manuscript" / relative
        module_name = f"Book.Chapters.Chapter{number:02d}"
        source = ROOT / "Book" / "Chapters" / f"Chapter{number:02d}.lean"
        if not chapter.is_file():
            missing_manuscript.append(number)
        if not source.is_file():
            missing_modules.append(number)
        elif module_name not in root_imports:
            missing_imports.append(number)
        else:
            covered.append(number)

    all_ids = [number for number, _ in chapters]
    duplicate_ids = sorted({n for n in all_ids if all_ids.count(n) > 1})
    dangling_imports = sorted(root_imports - {
        f"Book.Chapters.Chapter{n:02d}" for n in all_ids
    })

    def numbers(values: list[int]) -> str:
        return ", ".join(map(str, values)) if values else "none"

    lines = [
        "# Lean chapter coverage audit",
        "",
        f"- Manuscript chapters listed: **{len(chapters)}**",
        f"- Chapters with module files AND root imports: **{len(covered)}**",
        f"- Missing module files: **{len(missing_modules)}**",
        f"- Existing module files missing root imports: **{len(missing_imports)}**",
        f"- Missing manuscript files: **{len(missing_manuscript)}**",
        "",
        f"**Missing modules (chapter numbers):** {numbers(missing_modules)}",
        "",
        f"**Missing root imports (chapter numbers):** {numbers(missing_imports)}",
        "",
        f"**Missing manuscript files (chapter numbers):** {numbers(missing_manuscript)}",
        "",
        f"**Duplicate summary chapter numbers:** {numbers(duplicate_ids)}",
        "",
        "**Dangling Book.lean imports:** "
        + (", ".join(dangling_imports) if dangling_imports else "none"),
        "",
        "> Structural coverage does not certify that a module proves the claims, "
        "compiles, contains no `sorry`, or checks every code example in the chapter. "
        "Compilation is assessed separately in the Lean build workflow.",
    ]
    report = "\n".join(lines) + "\n"
    print(report)
    report_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if report_path:
        with open(report_path, "a", encoding="utf-8") as out:
            out.write(report)

    if missing_modules or missing_imports or missing_manuscript or duplicate_ids or dangling_imports:
        print(
            f"::warning title=Lean chapter coverage incomplete::"
            f"{len(missing_modules)} missing modules; "
            f"{len(missing_imports)} missing imports; "
            f"{len(missing_manuscript)} missing manuscript files"
        )
        return 1 if args.strict else 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
