# Editorial and formal-verification workflow

## Development

1. Draft exposition in `manuscript/chapters/part-NN/` and maintain the order in `manuscript/SUMMARY.md`. Recheck repository visibility before adding unpublished material.
2. Run `python scripts/extract_lean_examples.py` to check whether generated modules match the Markdown. To regenerate them after an intentional manuscript edit, use `python scripts/extract_lean_examples.py --write --force`; this replaces only generated files in `Book/Chapters/`.
3. Review the extracted modules and update `Book.lean` imports when the generator adds chapter modules. Interactive fragments and proof-state illustrations stay in Markdown unless rewritten as complete Lean examples.
4. Run `lake exe cache get` if pinned Mathlib artifacts are missing, then `lake build`. Do not run `lake update` unless intentionally changing dependency versions; review the manifest diff.
5. Review the changes with the author before committing or pushing, then inspect the **Verify Lean examples** GitHub Actions check.
6. Periodically evaluate Lean/Mathlib upgrades in a separate branch; never silently change versions halfway through an edition.

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
