# Advanced Mathematical Formalization in Lean 4

**Status:** Repository scaffolding. This is not yet a published textbook or a completed set of chapters.

An advanced textbook project for mathematicians who already know Lean 4. The goal is to explain practical and conceptual techniques for formalizing substantial mathematics, with executable examples and carefully versioned Mathlib dependencies.

## Layout

- `manuscript/` — eventual typeset textbook chapters; presently contains only an editorial note.
- `Book/` — Lean modules accompanying the chapters. `Book/Chapter01.lean` is a **build smoke test**, not an actual chapter.
- `Book.lean` — root module importing the chapter examples.
- `docs/EDITORIAL_WORKFLOW.md` — procedure for verifying and publishing material.
- `.github/workflows/lean.yml` — compile check on pushes and pull requests.
- `lean-toolchain` and `lakefile.lean` — pinned Lean/Mathlib setup.

## Prerequisites and build

Install [elan](https://github.com/leanprover/elan) and Git, then run in the repository root:

```sh
lake update
lake exe cache get
lake build
```

This initial project pins Lean and Mathlib to **v4.35.0**. After resolving dependencies, commit the generated `lake-manifest.json` so transitively referenced dependencies are reproducible.

The GitHub Actions workflow also attempts to build the Lean modules. **A successful Lean build is not a complete mathematical review**: all statements, assumptions, dependencies, and examples still require human verification.

## Manuscript, copyright, and publishing

**This repository is currently public. Do not upload unpublished or confidential manuscript chapters until its visibility has been changed to private and verified.**

No reuse license has been selected for this book or its text. Public visibility does not imply permission to republish the manuscript. Copyright and distribution terms should be settled before a public release, particularly if the book may be offered to an academic publisher.

The book's title, chapter structure, and publishing arrangements remain provisional.
