# Chapter 16 — Elaboration, Performance, and Proof Maintenance

> **Audience.** This chapter assumes you can work with Lean's goals and library. It explains how to diagnose elaboration errors, keep proof search and simplification efficient, and maintain formal developments as they grow.

Lean source is not checked directly as written. The parser builds syntax, macros expand notation, elaboration inserts implicit arguments and instances, and the kernel checks the resulting term. Understanding these stages helps distinguish a mathematical mistake from a name-resolution, typeclass, or elaboration problem.

Performance and maintenance are related. A proof that depends on broad unfolding or expensive search can become slower and more fragile as the environment grows. A proof built from small lemmas with clear interfaces is often both faster and easier to repair.

## Learning objectives

By the end of the chapter, you should be able to:

- distinguish parsing, elaboration, and kernel-checking failures;
- use expected types, explicit arguments, `#check`, and `#synth` to diagnose elaboration;
- reduce expensive simplification and repeated proof work;
- avoid fragile dependence on unfolding and automation search;
- use small lemmas and stable interfaces to manage proof performance;
- audit a development for placeholders, warnings, and unexpected axioms.

## 1. Lean processes source in stages

When Lean reports an error, identify the stage that failed. A simplified view of the pipeline is:

```text
source text
    │ parse
    ▼
syntax tree
    │ expand notation and macros
    ▼
elaborated terms with implicit arguments and instances
    │ check proof terms
    ▼
accepted declarations
```

A parser error usually points to syntax, indentation, or an unavailable notation. An unknown identifier points to name resolution or imports. A type mismatch means elaboration produced terms whose types do not match. A failed tactic leaves a proof goal unsolved. A kernel error means the produced term did not meet the declared type.

This classification keeps debugging focused. Adding a theorem cannot fix a misspelled identifier, and changing notation cannot fix a false mathematical statement. Read the earliest error first; later diagnostics may be consequences of it.

Some editor messages are warnings rather than errors. A warning may point to an unused variable, deprecated declaration, or a proof term that works but is not the intended interface. Treat warnings as information about the development's maintainability. Resolve them when they indicate dead context or a stale API, while distinguishing them from harmless project-specific style warnings.

## 2. Expected types guide elaboration

Lean often determines implicit arguments and overloaded operations from the expected type. If elaboration fails, provide that information locally with a type annotation or `show` statement.

For example, a numeral has many possible types. An expected type tells Lean which `OfNat` instance to use:

```lean
example : (3 : Int) + 4 = 7 := by
  norm_num
```

Without the annotation or surrounding expectation, Lean may infer a different numeric type than the theorem requires. Similarly, a polymorphic theorem can leave a type parameter unresolved until its result is checked against the goal.

Use `#check` to inspect a candidate's elaborated type and `#synth` to inspect the instance Lean can build. If an expression is underdetermined, pass named arguments explicitly or annotate the intermediate value. Prefer a small annotation near the ambiguity rather than qualifying every term in the proof.

### A type mismatch can expose a mathematical boundary

Some mismatches are not elaboration noise. `Nat` subtraction truncates at zero; integer subtraction does not. A vector of length `m+n` is not definitionally identical to one of length `n+m`. A `MonoidHom` preserves multiplication but does not promise injectivity. Before adding casts or coercions, ask whether the types encode a real difference that the theorem should address.

## 3. Separate the goal into smaller obligations

Large tactic blocks can obscure where a proof is difficult. Split the goal into named intermediate facts that isolate the source of the work:

```lean
example (n : Nat) : n + 1 ≤ n + 3 := by
  omega
```

A real intermediate fact should carry information the later proof uses. During exploration, temporary hypotheses and rewrites are useful, but before finalizing the theorem, remove unused steps and retain only the argument that expresses the reasoning.

For a genuinely complex argument, name a subgoal with a theorem or `have` statement that describes the mathematical fact needed next. This makes the proof easier to debug and can let the same fact be reused elsewhere.

## 4. Keep simplification and search focused

The simplifier can visit a large expression and use a large theorem set. Repeating the same broad call in many subgoals can cost time and make proofs sensitive to changes in global `[simp]` lemmas.

Use `simp` when the standard simplification behavior is intended. Add only the definitions or hypotheses needed. Use `simp only` when the exact rewrite set is important to the proof or when a large simp set is obscuring performance. `simp?` can help discover which rules were sufficient, but the suggested list should be reviewed for maintainability.

Avoid unfolding a large recursive definition throughout a theorem when a named equation lemma would expose only one branch. Avoid running expensive search tactics such as `exact?` in every subgoal of a large proof; use them to find a theorem, then make the application explicit.

If a simplifier call becomes slow, ask whether a rewrite rule increases term size, whether the same subexpression is being normalized repeatedly, and whether an abstract lemma can replace unfolding. Performance problems often point to a missing interface theorem rather than a need for a more elaborate tactic script.

The same principle applies to typeclass synthesis. If many declarations repeatedly infer the same large structure, factor the relevant assumption into a section variable or pass a named instance explicitly. If synthesis loops or searches too many candidates, reduce competing instances and avoid registering broad rules that generate more search branches. A local `letI` can isolate a temporary choice so later declarations do not inherit it.

Large expressions can also make kernel checking expensive even when tactic execution is quick. Repeatedly unfolding large definitions or building a giant proof term from one monolithic tactic can increase checking cost. Break the proof at meaningful lemmas: the resulting terms are smaller, and each theorem can be checked and cached independently in its module.

## 5. Definitional transparency and abstraction

Lean can reduce transparent definitions when checking whether two expressions are definitionally equal. This is useful for computation, but proofs that rely on unfolding many implementation details can be brittle or expensive. A function may change its implementation while preserving the same public equations and theorems.

Use `rfl` when the equality follows by computation or definitional unfolding. Use a named equation theorem when the result is propositionally equal but not definitionally reducible. Use an abstract theorem when the client should not depend on the implementation at all.

This gives a hierarchy of proof dependencies:

```text
implementation details
        │ more stable
        ▼
defining equations
        │ more abstract
        ▼
mathematical specification and API laws
```

Choose the highest layer that supplies the fact you need. This reduces coupling and often reduces elaboration work because Lean does not have to unfold unrelated definitions to compare terms.

## 6. Proof terms and trust boundaries

Tactics construct proof terms; they do not bypass the kernel's type checking. A tactic can search, simplify, or calculate, but Lean ultimately checks that the resulting term has the requested proposition as its type.

This is why `simp`, `ring`, and `omega` can be used for proof automation while preserving a small trusted kernel. The tactic implementation may be complex, but its output is checked. The mathematical statement still matters: an automation tactic proves the goal that was written, not the goal the author intended to write.

When auditing a theorem, inspect its statement and check for placeholders such as `sorry`. The command `#print axioms theoremName` can show which axioms a theorem depends on. This is useful when a result crosses trust boundaries or when a project has strict assumptions about classical choice or imported axioms.

Proof automation is not the same as testing a program. If a theorem is intended to characterize executable code, prove the specification and separately inspect the computational behavior that users will run. Definitions marked `partial`, `unsafe`, or `noncomputable` have different computational interfaces and should be used deliberately.

## 7. Performance through theorem architecture

The strongest performance improvements often come from reorganizing the mathematical development:

- prove a recursive equation once rather than unfolding the function repeatedly;
- package an invariant into a subtype or indexed family when many theorems use it;
- use a generic homomorphism theorem rather than reproving preservation for each map;
- normalize a large expression at a well-defined boundary;
- split a large theorem into reusable lemmas whose statements constrain elaboration.

These changes reduce duplicate work and give Lean more precise expected types. They also improve the human cost of maintenance: when a definition changes, the equations and interface theorems isolate which downstream results need attention.

A shorter proof is not always faster, and a faster proof is not always clearer. A broad tactic may close a goal quickly today but search much more of the environment after future imports. A named theorem application may use more lines but make elaboration deterministic. Measure performance when it matters, but optimize for stable proof boundaries before micro-optimizing syntax.

## 8. A debugging workflow

When a file stops elaborating or becomes unexpectedly slow, use a controlled sequence:

1. Read the first error and classify the failing stage.
2. Reduce the problem to the smallest declaration that still exhibits it.
3. Inspect the target and local context in the editor.
4. Check candidate theorem types with `#check` and instances with `#synth`.
5. Replace broad automation with one named rewrite or intermediate fact.
6. Rebuild the surrounding module to identify downstream dependencies.
7. After the repair, remove temporary experiments and warnings.

The minimal example is especially valuable for typeclass and elaboration failures. It reveals whether the cause is local syntax, an import, a conflicting instance, or a theorem assumption that was never available.

Do not respond to a failed tactic by adding more automation before understanding the goal. A script that suppresses the symptom can make the eventual repair harder and can accidentally prove a weaker or different statement than intended.

### Change one boundary at a time

When updating a library dependency, avoid rewriting every affected proof at once. First inspect the declaration that changed and compare its old and new types. Add a small compatibility lemma if that keeps the rest of the development stable. Then migrate one module at a time and rebuild its dependents.

This method makes regressions easier to localize. If a proof fails immediately after one interface lemma changes, the failure points to a mismatch at that boundary. If many imports, definitions, and tactics change together, the error may be several layers removed from its cause.

Keep a concise record of project-level conventions that are easy to forget: the expected Mathlib version, whether examples assume `import Mathlib`, naming conventions for public equations, and which modules are intended to stay foundational. A short project note is more reliable than asking every maintainer to infer those rules from old proof scripts.

### Review the final declarations

After a repair, inspect the theorem signature and the resulting proof term when the change was substantial. Confirm the statement still includes the intended hypotheses and that no temporary assumption was left in a section. Use `#print axioms` for results whose trust assumptions matter. Remove `sorry`, debugging commands, and unused local instances before publishing a module.

This review is especially valuable after a large refactor. A file can compile while an unintended generalization, stronger assumption, or classical dependency has entered the public API. Checking signatures and assumptions catches these changes before downstream users rely on them.

## 9. Maintainable proof style

Keep theorem statements focused. Name helper lemmas for repeated facts. Give public declarations stable names and docstrings. Prefer explicit theorem applications when they reveal the mathematical step, and use automation where the routine calculation is genuinely secondary.

Review warnings. Unused section variables may indicate that a theorem signature is carrying unnecessary context. Unreachable or deprecated declarations may signal a stale interface. A growing import list can reveal that a foundational theorem has been placed in the wrong module.

When a project updates Lean or Mathlib, first identify the changed declaration or behavior. Search the new API, compare types, and update the smallest abstraction boundary possible. A development built around named equations and bundled interfaces is easier to migrate than one that unfolds internal definitions everywhere.

For a larger project, review module boundaries as part of maintenance. A small change to a foundational file can trigger recompilation of every dependent module. If that file contains unrelated applications, split them so the frequently used core has a smaller dependency surface. Keep the public interface stable even when implementation modules are reorganized.

## 10. Common failure modes

### A parser error is treated as a theorem error

Fix syntax and imports before changing the mathematical statement. Later errors may disappear after the first parse failure is resolved.

### A type mismatch is patched with an unexplained cast

Inspect whether the types differ mathematically. Add a proof of index equality, adjust the theorem statement, or choose the correct structure rather than hiding the mismatch.

### Broad simplification unfolds a large implementation

Use an equation lemma or abstract theorem. Keep unfolding local to the branch under consideration.

### Search tactics remain in a public proof

Use search to discover declarations, then state the dependency explicitly. This reduces sensitivity to the imported environment.

### Temporary proof steps are left behind

Remove unused hypotheses, redundant rewrites, and comments that describe an abandoned proof attempt. The final script should communicate the chosen argument.

### Performance is optimized before the theorem is understood

First make the statement and proof structure clear. Then measure the expensive part and optimize that boundary without weakening the theorem.

## 11. Exercises

1. Take an elaboration error from a development and classify whether it arose in parsing, name resolution, typeclass synthesis, or proof completion.
2. Use `#check` and `#synth` to diagnose an underdetermined theorem application.
3. Refactor a proof that repeatedly unfolds a recursive definition to use one named equation theorem.
4. Replace a broad `simp [*]` call with a focused rewrite or `simp only` call and explain the tradeoff.
5. Use `#print axioms` on a theorem in a project and record the result. Explain which assumptions are acceptable for that project.
6. Identify a typeclass or import dependency that makes a file elaborate differently when moved. Make the dependency local or explicit.
7. Take a proof script with exploratory steps and remove every step that does not contribute to the final proof term.

## Summary

Lean parses, elaborates, and then kernel-checks declarations. Classify errors by stage, provide expected types where inference is ambiguous, and inspect typeclass search with `#synth`. Keep automation focused, use public equations and API laws instead of broad unfolding, and optimize theorem architecture before micro-optimizing tactics. Named interfaces, small lemmas, and explicit dependencies make large developments faster to understand and easier to maintain.

## Further reading

- [Lean reference: Elaboration and Compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
- [Lean reference: Type Classes](https://lean-lang.org/doc/reference/latest/Type-Classes/)
- [Lean reference: Validating Proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

