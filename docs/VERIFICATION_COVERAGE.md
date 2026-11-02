# Chapter verification coverage

The book has 120 numbered manuscript chapters. On 2026-11-01, only **37** numbered
`Book/Chapters/ChapterNN.lean` modules existed; the other **83** lacked such a module.
The initial extraction script selected only fenced Lean examples that began with
standalone top-level commands. Several later chapters contain mostly prose,
inline identifiers, mathematics, or illustrative text, and supply **no executable
Lean examples** to extract. This is an *editorial/formalization gap*, not evidence
that 83 external Lean packages are missing.

## Status categories

1. **Manuscript only** — chapter exists, but no verified Lean module is present.
2. **Module exists** — a corresponding source file is present and imported in `Book.lean`.
3. **Compiles** — automated Lean CI builds the module with pinned Lean/Mathlib.
4. **Proof-audited** — all relevant statements, assumptions, `sorry` / `admit`
   usage, and displayed examples have been independently checked.
5. **Chapter-reviewed** — a mathematically qualified reviewer confirms the
   exposition and the formalization agree.

Only statuses 2–3 are currently covered by automated tests. In particular,
**a green build never means that all 120 chapters are verified**.

## Monitoring

`python scripts/check_chapter_coverage.py` prints a coverage report.
GitHub Actions runs it on each push and displays the missing chapter numbers
as an informational warning, without failing the build while work is ongoing.
Once every chapter has a genuine source module and a root import,
`python scripts/check_chapter_coverage.py --strict` can be made a required gate.

## Closing a chapter gap

For each chapter without a source module:

1. Inspect the mathematical claims and example references in its Markdown source.
2. Create `Book/Chapters/ChapterNN.lean` with **substantive, executable** examples
   or theorems *relevant to that chapter*; do not produce empty placeholder files.
3. Use focused Mathlib imports when feasible, explicitly naming dependencies and
   avoiding unnecessary full-library imports.
4. Add `public import Book.Chapters.ChapterNN` in `Book.lean`.
5. Build with the pinned toolchain; verify the intended theorem statements, not
   just that some code compiles.
6. Keep an index mapping the manuscript's displayed code to the verified source,
   noting any fragments or conceptual claims that have not been formalized.
7. Record independent mathematical review separately from compilation status.

The existing extractor, `scripts/extract_lean_examples.py`, is a starting point,
not a complete guarantee of code coverage. It ignores Markdown snippets that are
not standalone commands, so missing modules require manual formalization.
