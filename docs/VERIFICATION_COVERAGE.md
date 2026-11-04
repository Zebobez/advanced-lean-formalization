# Chapter verification coverage

The manuscript lists **120 numbered chapters**. Every chapter now has a corresponding `Book/Chapters/ChapterNN.lean` module imported by `Book.lean`, and the strict structural audit passes. The extractor currently produces 116 modules containing **411 complete Lean command blocks**. For the remaining 4 chapters, supplemental finite-model examples were added; the [manual model index](../Book/Chapters/MANUAL_MODEL_INDEX.md) maps each to its chapter source.

## What the checks establish

- **Structural coverage:** all 120 manuscript chapters have a Lean source module and root import.
- **Compilation:** `lake build` compiles the root library with the pinned Lean and Mathlib versions. The chapter CI uses the same root build.
- **Executable examples:** extracted commands and the supplemental finite examples compile. The extractor still records **5 contextual fragments** in Chapters 1 and 26 that are not standalone Lean commands.

Compilation does not certify every mathematical claim, every prose exercise, or every displayed fragment in the manuscript. In particular, supplemental finite examples check selected computations and invariants; they do not establish general probability, queueing, or optimization theorems. No independent mathematical proof audit or chapter review is claimed here.

## Toolchain and packages

- Lean: `leanprover/lean4:v4.35.0` (`lean-toolchain`)
- Mathlib: `v4.35.0` (`lakefile.lean` and `lake-manifest.json`)
- Transitive Lake dependencies: pinned by `lake-manifest.json`

The root `Book` library is the build target, so all imported chapter modules participate in CI. `scripts/check_chapter_coverage.py --strict` fails if a listed manuscript chapter lacks a module or root import.

## Maintaining coverage

1. Add complete displayed Lean commands to the extracted module or a focused, chapter-specific module.
2. Keep contextual proof-state snippets in the manuscript labeled as illustrations unless converted to complete Lean commands.
3. Add each chapter module to `Book.lean` and update the appropriate extraction or supplemental index.
4. Run `python scripts/check_chapter_coverage.py --strict` and `lake build` with the pinned toolchain.
5. Record proof auditing and chapter review separately from compilation.
