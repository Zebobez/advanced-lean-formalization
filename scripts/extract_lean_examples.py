from __future__ import annotations

import argparse
import re
from pathlib import Path

FENCE = re.compile(chr(96) * 3 + r"([^\n]*)\n(.*?)\n" + chr(96) * 3, re.S)
MODIFIERS = {"private", "protected", "noncomputable", "unsafe", "partial", "local", "scoped", "mutual"}
COMMANDS = {
    "import", "theorem", "lemma", "def", "abbrev", "structure", "inductive", "class",
    "instance", "example", "namespace", "section", "end", "open", "universe",
    "universes", "variable", "variables", "attribute", "set_option", "syntax",
    "macro", "elab", "initialize", "notation", "opaque", "axiom", "classical",
}


def roman_to_int(value: str) -> int:
    values = {"I": 1, "V": 5, "X": 10, "L": 50, "C": 100, "D": 500, "M": 1000}
    total = previous = 0
    for char in reversed(value):
        current = values[char]
        total += -current if current < previous else current
        previous = max(previous, current)
    return total


def starts_with_command(source: str) -> bool:
    for line in source.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        while stripped.startswith("@[") and "]" in stripped:
            stripped = stripped[stripped.index("]") + 1 :].lstrip()
        tokens = stripped.split()
        while tokens and tokens[0] in MODIFIERS:
            tokens = tokens[1:]
        if not tokens:
            continue
        if tokens[0] in COMMANDS:
            return True
        if re.fullmatch(r"#[A-Za-z][A-Za-z0-9_]*", tokens[0]):
            return True
        return False
    return False


def dedupe_universe_commands(source: str, declared: set[str]) -> str:
    output: list[str] = []
    command = re.compile(r"^(\s*universes?)\s+(.+?)\s*$")
    for line in source.splitlines():
        match = command.match(line)
        if not match:
            output.append(line)
            continue
        names = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", match.group(2))
        fresh = [name for name in names if name not in declared]
        declared.update(names)
        if fresh:
            output.append(f"{match.group(1)} {' '.join(fresh)}")
    return "\n".join(output)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract complete top-level Lean commands from the manuscript into Book/Chapters."
    )
    parser.add_argument("--write", action="store_true", help="write missing generated files")
    parser.add_argument("--force", action="store_true", help="replace existing generated files")
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    summary_path = root / "manuscript" / "SUMMARY.md"
    summary = summary_path.read_text(encoding="utf-8")
    toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    lakefile = (root / "lakefile.lean").read_text(encoding="utf-8")
    mathlib_match = re.search(r'mathlib4"\s*@\s*"([^"]+)"', lakefile)
    mathlib_ref = mathlib_match.group(1) if mathlib_match else "unspecified"

    part = 0
    total_selected = 0
    total_skipped = 0
    module_outputs: list[tuple[Path, str, int, int]] = []
    index_rows: list[str] = []
    for line in summary.splitlines():
        part_match = re.match(r"^# Part ([IVXLCDM]+)\b", line)
        if part_match:
            part = roman_to_int(part_match.group(1))
            continue
        chapter_match = re.match(r"^- \[Chapter (\d+)[^\]]*\]\(([^)]+\.md)\)$", line)
        if not chapter_match:
            continue
        number = int(chapter_match.group(1))
        chapter_path = root / "manuscript" / chapter_match.group(2).replace("/", "\\")
        if not chapter_path.is_file():
            raise SystemExit(f"Missing manuscript chapter: {chapter_path}")
        text = chapter_path.read_text(encoding="utf-8")
        title_match = re.search(r"^# Chapter \d+\s*[—-]\s*(.+)$", text, re.M)
        title = title_match.group(1).strip() if title_match else f"Chapter {number}"
        blocks = FENCE.findall(text)
        selected: list[tuple[int, str]] = []
        skipped: list[int] = []
        declared_universes: set[str] = set()
        extra_imports: set[str] = set()
        for fence_number, (language, body) in enumerate(blocks, 1):
            if language.strip().lower() not in {"lean", "lean4"}:
                continue
            if not starts_with_command(body) or re.search(
                r"(?m)^\s*(?:\.\.\.|sorry|admit|by\s*\?)\s*(?:--.*)?$", body
            ):
                skipped.append(fence_number)
                continue
            body_lines: list[str] = []
            for body_line in body.splitlines():
                import_match = re.match(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)\s*$", body_line)
                if import_match:
                    if import_match.group(1) != "Mathlib":
                        extra_imports.add(import_match.group(1))
                    continue
                body_lines.append(body_line)
            body = "\n".join(body_lines)
            body = dedupe_universe_commands(body, declared_universes)
            selected.append((fence_number, body.rstrip()))
        total_selected += len(selected)
        total_skipped += len(skipped)
        if not selected:
            if skipped:
                index_rows.append(f"- Chapter {number}: no complete command extracted; contextual fragments in fences {', '.join(map(str, skipped))}.")
            continue

        module_name = f"Chapter{number:02d}"
        module_path = root / "Book" / "Chapters" / f"{module_name}.lean"
        combined = "\n".join(body for _, body in selected)
        chapter_namespace = re.search(rf"(?m)^\s*namespace\s+Chapter0*{number}\b", combined)
        dependencies = sorted({
            int(match.group(1))
            for match in re.finditer(r"\bChapter0*(\d+)\.", combined)
            if int(match.group(1)) != number
        })
        imports = [f"public import Book.Chapters.Chapter{dependency:02d}" for dependency in dependencies]
        imports.extend(f"public import {name}" for name in sorted(extra_imports))
        pieces = [
            "module",
            "",
            *imports,
            "public import Mathlib",
            "",
            "public section",
            "",
            "/-!",
            f"# Chapter {number} — {title}",
            "",
            f"Extracted from {chapter_path.relative_to(root).as_posix()}.",
            f"Generated for {toolchain} and Mathlib ref {mathlib_ref}.",
            "Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.",
            "-/",
            "",
        ]
        if not chapter_namespace:
            pieces.extend([f"namespace Book.Chapters.{module_name}", ""])
        for fence_number, body in selected:
            pieces.append(f"-- Source Lean fence {fence_number}")
            pieces.append(body)
            pieces.append("")
        if not chapter_namespace:
            pieces.append(f"end Book.Chapters.{module_name}")
        pieces.append("")
        module_outputs.append((module_path, "\n".join(pieces), len(selected), len(skipped)))
        omitted = f"; contextual fragments left in manuscript fences {', '.join(map(str, skipped))}" if skipped else ""
        index_rows.append(
            f"- Chapter {number}: {module_path.relative_to(root).as_posix()} — {len(selected)} command blocks extracted{omitted}."
        )

    index_path = root / "Book" / "Chapters" / "EXTRACTION_INDEX.md"
    index_text = "\n".join([
        "# Lean example extraction index",
        "",
        f"Source: manuscript/SUMMARY.md; compiler pin: {toolchain}; Mathlib ref: {mathlib_ref}.",
        "",
        "The generator copies only Lean fences that begin with a complete top-level command. Type-expression illustrations, interactive tactic fragments, proof-state illustrations, and blocks containing literal placeholders such as ellipses or sorry stay in the Markdown source until they are incorporated into a complete executable example.",
        "",
        "Supplemental finite-model modules authored for chapters without extracted commands are listed in [MANUAL_MODEL_INDEX.md](MANUAL_MODEL_INDEX.md). These examples illustrate selected calculations and are not complete formalizations of the chapters.",
        "",
        *index_rows,
        "",
    ])
    outputs = [(path, content) for path, content, _, _ in module_outputs] + [(index_path, index_text)]
    missing = [path for path, _ in outputs if not path.exists()]
    stale = [path for path, content in outputs if path.exists() and path.read_text(encoding="utf-8") != content]
    if not args.write:
        if missing or stale:
            print(f"Generated modules: {len(module_outputs)}; missing: {len(missing)}; stale: {len(stale)}. Re-run with --write to create missing files.")
            for path in missing[:20]:
                print(f"MISSING {path.relative_to(root)}")
            for path in stale[:20]:
                print(f"STALE {path.relative_to(root)}")
            return 1
        print(f"Lean example extraction is current: {len(module_outputs)} modules.")
        return 0

    if not args.force:
        existing = [path for path, _ in outputs if path.exists()]
        if existing:
            raise SystemExit("Refusing to replace generated files without --force: " + ", ".join(str(p.relative_to(root)) for p in existing))
    for path, content in outputs:
        if path.exists() and path.read_text(encoding="utf-8") == content:
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8", newline="\n")
    print(f"Wrote {len(module_outputs)} modules, extracting {total_selected} Lean command blocks; left {total_skipped} contextual fragments in Markdown.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
