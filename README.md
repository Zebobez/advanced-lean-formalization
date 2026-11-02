# Advanced Mathematical Formalization in Lean 4

**Status:** The 120-chapter manuscript is staged in this repository. Executable examples have been extracted for chapters with complete Lean command blocks and still require full verification and editorial review.

An advanced textbook project for mathematicians who already know Lean 4. The goal is to explain practical and conceptual techniques for formalizing substantial mathematics, with executable examples and carefully versioned Mathlib dependencies.

## Layout

- `manuscript/` — Markdown master, organized into 23 part folders with `SUMMARY.md`.
- `Book/Chapter01.lean` — preserved build smoke test; `Book/Chapters/` contains executable chapter examples.
- `scripts/extract_lean_examples.py` — copies complete Lean command blocks from the manuscript into generated modules.
- `Book.lean` — root module importing the smoke test and extracted chapter modules.
- `docs/EDITORIAL_WORKFLOW.md` — procedure for verifying and publishing material.
- `.github/workflows/lean.yml` — compile check on pushes and pull requests.
- `lean-toolchain` and `lakefile.lean` — pinned Lean/Mathlib setup.

## Prerequisites and build

Install [elan](https://github.com/leanprover/elan) and Git. With the pinned toolchain selected, run in the repository root:

```sh
lake exe cache get
lake build
```

This project pins Lean and Mathlib to **v4.35.0**. Use `lake update` only when intentionally changing dependencies; review the resulting `lake-manifest.json` before staging it.

The GitHub Actions workflow also attempts to build the Lean modules. **A successful Lean build is not a complete mathematical review**: all statements, assumptions, dependencies, and examples still require human verification.

## Manuscript, copyright, and publishing

**Repository visibility was verified as private on 2026-11-01. Recheck it before sharing or adding future unpublished material.**

No reuse license has been selected for this book or its text. Copyright and distribution terms should be settled before a public release, particularly if the book may be offered to an academic publisher.

The book's title, chapter structure, and publishing arrangements remain provisional.
