# Editorial and formal-verification workflow

## Development

1. Draft mathematical exposition in `manuscript/` (only after the repository is confirmed private).
2. Put all executable chapter examples in `Book/ChapterNN.lean`, and import them from `Book.lean`.
3. Run `lake update`, `lake exe cache get`, and `lake build`. Commit the resulting `lake-manifest.json` when dependency resolution is complete.
4. Push changes and inspect the **Verify Lean examples** GitHub Actions check.
5. Periodically evaluate Lean/Mathlib upgrades in a separate branch; never silently change versions halfway through an edition.

## Verification before release

- Check that every displayed Lean fragment appears in, or is reproducible from, the checked sources.
- Review the exact theorem statements and hypotheses: compiling a theorem does not establish that it says what the exposition claims.
- Audit for `sorry`, `admit`, unsafe assumptions, new axioms, and opaque escape hatches. The current CI checks compilation only, **not** proof completeness.
- Check mathematical explanations, bibliographic references, and pedagogical exercises independently of AI assistance.
- Obtain reviews from experienced Lean/Mathlib users and domain mathematicians.
- Decide manuscript copyright, repository licenses, and publisher embargo/exclusivity terms before releasing text publicly.

## Suggested publication deliverables

- A professionally typeset PDF or print master.
- Verified Lean source files with a pinned toolchain and committed Lake manifest.
- A documented change log for edition-specific updates.

This file is a planning document; it does not certify that any chapter has been formally or editorially reviewed.
