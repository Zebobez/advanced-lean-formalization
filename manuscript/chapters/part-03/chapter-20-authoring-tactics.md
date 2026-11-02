# Chapter 20 — Authoring Tactics with Macros and Elaborators

> **Audience.** This chapter assumes you can read tactic scripts and have encountered Lean syntax quotations. It introduces the design choices behind small custom tactics, from syntax macros to goal-inspecting elaborators, and explains how to keep proof-producing automation predictable.

When a proof pattern recurs, there are three possible responses. A theorem may capture a mathematical fact; a helper tactic may capture a sequence of existing proof steps; or a new elaborator may inspect the goal and construct a proof algorithmically. The first is usually best when the reusable content is mathematics. The second is often enough when the task is syntactic organization. The third is justified when the tactic must inspect types, local hypotheses, or expressions to decide what proof to build.

This chapter focuses on the boundary between these choices. The aim is not to replace Lean's standard tactics with a private collection. It is to learn how to package a stable pattern without adding unnecessary metaprogramming complexity.

## Learning objectives

By the end of the chapter, you should be able to:

- distinguish a tactic macro from a tactic elaborator;
- define a hygienic tactic macro using syntax quotations;
- inspect a goal with `TacticM` and report useful information;
- understand the roles of `Syntax`, `Expr`, metavariables, and proof terms;
- design a custom tactic that has a narrow contract and useful errors.

## 1. Choose the lightest abstraction

Before writing tactic code, identify what is actually repeated. If several proofs use the same mathematical lemma, name a theorem. If they repeat a predictable sequence such as `constructor` followed by a common finishing step, write a macro that expands to that sequence. If success depends on examining the target or context and selecting among proof constructions, use an elaborator or a metaprogram in `TacticM`.

```text
repeated content
      │
      ├── mathematical fact ───────────► theorem / lemma
      ├── fixed tactic sequence ───────► tactic macro
      └── inspect goal, build proof ───► tactic elaborator
```

This hierarchy is a maintenance tool. Theorem statements give mathematical reuse to ordinary Lean declarations and search. Macros add syntax but delegate all reasoning to existing tactics. Elaborators can implement new proof procedures, but they must manage syntax, goals, expressions, errors, and performance.

## 2. A tactic macro is syntax translation

A tactic macro introduces a new syntax form and expands it into existing tactic syntax. It does not need to inspect the goal or manipulate proof terms. Lean's quotations let the macro author write the expansion in familiar syntax rather than manually constructing a syntax tree.

```lean
import Lean

syntax "assumption_or_rfl" : tactic

macro_rules
  | `(tactic| assumption_or_rfl) => `(tactic| first | assumption | rfl)

example (p : Prop) (hp : p) : p := by
  assumption_or_rfl

example (n : Nat) : n = n := by
  assumption_or_rfl
```

The macro has a deliberately small contract: try the local assumptions first, then reflexivity. The proof work is performed by `first`, `assumption`, and `rfl`. If both branches fail, the failure comes from the expanded tactic sequence, so the user sees familiar Lean behavior.

The quotation begins with `` `(tactic| ... ) `` to make the syntactic category explicit. The pattern quotation on the left matches the new tactic; the quotation on the right constructs the tactic sequence. Tactic macros should explicitly state this category. An unqualified quotation may be parsed as a term or command instead of as tactic syntax.

The macro is hygienic: identifiers introduced by macro expansion do not accidentally capture unrelated names at the call site. In this example, the tactic references built-in syntax, and no local identifier needs to be generated. Hygiene lets the macro be moved into a module and reused without changing the meaning of a proof based on its surrounding names.

## 3. Macros with arguments

Antiquotations splice matched syntax into a quotation. A macro can accept an existing tactic sequence and add a fallback:

```lean
syntax "try_then_assumption " tacticSeq : tactic

macro_rules
  | `(tactic| try_then_assumption $firstTac:tacticSeq) =>
      `(tactic| first | $firstTac | assumption)
```

Now a call such as `try_then_assumption rfl` tries the supplied sequence first and falls back to `assumption` if it fails. The antiquotation `$firstTac:tacticSeq` captures a tactic sequence, and the expansion inserts that syntax into another tactic quotation.

This example is syntactic convenience, not a new proof method. The macro should only be kept if it helps a project express a recurring policy clearly. A short macro that merely renames an existing tactic can make code less discoverable. Good syntax compresses a stable convention; it should not force users to learn a private vocabulary for ordinary Lean steps.

### Macro recursion and backtracking

Macros are expanded as tactic execution reaches them, so recursive tactic macros can be written when the recursion is guarded by tactic failure or another execution step. This is more subtle than a simple text substitution: expansion may succeed syntactically while the resulting tactic later fails, allowing another macro expansion to be tried. For this reason, a macro that tries alternatives should normally delegate to `first` rather than reimplementing fallback behavior through multiple macro rules.

When a recursive macro is appropriate, identify the tactic operation that makes progress and explain why recursion eventually stops. The same progress discipline used for `repeat` in Chapter 17 applies here. Macro recursion that expands without executing a tactic capable of failing can loop during elaboration.

## 4. From syntax to goal state

An elaborator handles a syntax form directly. A tactic elaborator runs in `TacticM`, which has access to Lean's tactic state and supports interaction with the metaprogramming layer. It can inspect the current goal, read local declarations, run existing tactics, and produce or assign proof terms.

The main data objects have different roles:

- `Syntax` represents parsed user text, including tactic and term syntax.
- `Expr` represents elaborated expressions in Lean's core language.
- A metavariable is an unknown expression to be solved during elaboration. A tactic goal is a metavariable together with a local context and a target type.
- `MVarId` identifies such a metavariable and provides operations for inspecting or assigning it.
- `TacticM` manages the active goal list, messages, and tactic execution state.

The transformation is roughly:

```text
user tactic syntax
       │ parse
       ▼
Syntax ── tactic elaborator ──► TacticM
                                  │ inspect target / context
                                  │ construct or run proof steps
                                  ▼
                          assigned goals + proof terms
                                  │
                                  ▼
                             kernel check
```

The kernel still checks the term that closes the theorem. A custom tactic is not a substitute for proof checking. However, its implementation can be wrong, unexpectedly expensive, or too permissive about which declarations it uses. Tactic authors therefore need both a sound proof construction and a clear behavioral contract.

One useful implementation discipline is to separate observation from mutation. First read the target and local context without changing the goal list. Decide which case applies and validate the required syntax. Only then run a tactic or assign a proof. This order makes failures easier to diagnose: an unsupported goal is rejected before partial proof state has been constructed. If the tactic needs backtracking, use the tactic framework's supported error handling rather than catching every exception indiscriminately; an internal programming error should not be converted into a misleading “no proof found” message.

## 5. A diagnostic tactic that inspects the target

Before implementing a search procedure, it is useful to learn how a tactic reads the current goal. The following tactic reports the target without changing it:

```lean
import Lean

open Lean Elab Tactic

elab "report_target" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  logInfo m!"target: {target}"
```

The declaration associates the syntax `report_target` with an elaboration action. `getMainGoal` retrieves the first active goal; `getType` reads its target expression; and `logInfo` emits a message in the editor. Since the tactic does not assign the goal or replace the goal list, the proof must continue afterward:

```lean
example (n : Nat) : n = n := by
  report_target
  rfl
```

This is a diagnostic tactic. It demonstrates the boundary between surface syntax and the expression that Lean is actually asked to prove. A useful diagnostic should label its output and avoid polluting the environment or changing the proof state.

The expression printed by `logInfo` may not resemble the source exactly. Implicit arguments, notation, coercions, and elaborated typeclass operations can appear explicitly or use internal names. That is expected: syntax is for the author, while the `Expr` is the term structure on which metaprograms operate.

Diagnostics are also a safe first metaprogramming project because they do not assign metavariables. A solver has a stronger obligation: the expression it assigns must have exactly the target type in the goal's local context. When that context contains dependent hypotheses, moving a proof term between goals or reconstructing a binder manually can invalidate it. Prefer operations on the goal identifier that preserve the context, and let Lean report a type mismatch at the point where an assignment is attempted.

## 6. Elaborators should delegate when possible

Suppose the desired behavior is simply to run an existing tactic sequence. A macro is the right tool. If a tactic must inspect the goal to choose a sequence, it can often still delegate the proof work back to Lean's tactic interpreter. A tactic elaborator can build syntax with a quotation and pass it to `evalTactic` rather than constructing the proof term directly.

This layered approach keeps responsibilities clear:

1. inspect the goal or context to choose a strategy;
2. invoke standard tactics for the chosen branch;
3. let those tactics create proof terms;
4. allow the kernel to check the result.

Direct expression construction is appropriate when an algorithm naturally computes an `Expr` proof or when the existing tactic language does not provide the needed operation. It is a higher complexity boundary: the implementation must handle binders, local contexts, universe levels, coercions, and metavariables correctly. The tactic reference and Lean's own tactic implementations are useful guides, but APIs should be checked against the Lean version targeted by the project.

An elaborator should also distinguish a missing solution from unsupported input. For example, a ring normalizer may decide that the reified sides differ, which is evidence that this identity is false in the selected ring theory; a parser that cannot recognize a new operation merely lacks support for that syntax. Reporting those cases differently helps users determine whether to fix the theorem or extend the tactic. A tactic should not claim a proposition is false solely because its search procedure failed.

Do not confuse “uses metaprogramming” with “bypasses the kernel.” A tactic can inspect arbitrary syntax and perform complicated search, yet its assigned proof term is still checked. But other features, such as native evaluation admitting a result through an axiom, alter the trust assumptions; Chapter 19 treats that boundary separately.

## 7. Error messages and failure behavior

A tactic should fail early when its preconditions are not met and explain the relevant condition. If a tactic applies only to equalities, check the target shape before running a specialized algorithm. If an expression is unsupported, report what forms are supported rather than returning a cryptic internal error.

Failure behavior is part of the tactic API. A tactic that silently succeeds while leaving the goal unchanged can mislead readers, especially when its name promises a solution. Diagnostic tactics are an exception, but their names and messages should make their non-solving role clear. A solving tactic should either close its intended goals or fail with a useful explanation.

When a tactic creates subgoals, preserve their logical relationship to the original target. Use the standard tactic combinators or established goal APIs where possible, because Lean manages goal lists and metavariable assignment. Avoid mutating goal state in multiple inconsistent ways. A clear invariant for a tactic's internal state makes failures reproducible.

## 8. Scope and import discipline

Custom tactics should live in a module that reflects their purpose. A project-specific macro can be local to a file or namespace if its syntax is not intended as a public interface. A general tactic belongs in a module whose dependencies are reasonable for its clients. Importing a large metaprogramming module into every mathematics file can increase compile time and expose more syntax than necessary.

Avoid introducing a global tactic alias for a name already used by core Lean or Mathlib. Choose distinctive syntax, document the import that provides it, and keep examples near the definition. If a tactic depends on a specific Mathlib rule set or theorem family, make that dependency explicit so a user can understand why the import is required.

As with the attributes discussed in Chapter 15, tactic syntax is an API decision. Once downstream files depend on it, changing its behavior can break proofs even when its surface syntax remains the same. Prefer small, stable contracts over tactics that attempt to be “helpful” in many unrelated situations.

## 9. Common failure modes

### The quotation is interpreted in the wrong syntax category

Use an explicit category, such as `` `(tactic| ... ) ``, for tactic syntax. Match the category on both the macro input and the generated output.

### A macro duplicates the tactic language

Delegate to `first`, `<;>`, or another existing combinator. Write a macro only when it names a stable policy or removes a meaningful repeated pattern.

### A macro references names from the call site unexpectedly

Review hygiene and how identifiers are introduced. Prefer quotations and antiquotations over constructing raw identifiers or manipulating syntax internals.

### An elaborator prints the target but leaves users confused

Label diagnostic output and make it clear whether the tactic changes the goal. A reporting tactic should not look like a solver.

### A tactic works for one expression but fails after notation changes

Inspect elaborated `Expr` structure and types rather than matching surface text. Add explicit support for the intended operations and reject other forms with a useful message.

### The tactic closes goals using hidden assumptions

Define which hypotheses it may use and expose key choices. A tactic should not unexpectedly depend on unrelated local declarations or broad global search behavior.

## 10. Exercises

1. Define a tactic macro that runs `constructor` and then `assumption` on each generated goal. State exactly which theorem shapes it supports.
2. Extend a macro to accept a tactic argument through an antiquotation. Explain which parts are syntax and which parts are executed later.
3. Implement a diagnostic tactic that reports both the target and the number of local declarations. Use the current Lean API documentation to find the relevant context operation.
4. Convert a repeated proof script into a tactic macro. Then decide whether a theorem would be a better abstraction and justify the choice.
5. Sketch an elaborator that recognizes an equality target and delegates to `rfl` only when both sides are definitionally equal. Identify the expression and goal operations it would need.
6. Give an example of an unsupported syntax form and write the error message a well-designed tactic should report.
7. Design a small project tactic with a narrow contract. Document its syntax, preconditions, imports, and whether it can leave subgoals.

## Summary

Use a theorem for reusable mathematics, a tactic macro for a fixed tactic sequence, and an elaborator when the strategy depends on inspecting the goal or context. Make tactic quotations explicit, rely on hygiene, and delegate to existing tactics where possible. A `TacticM` elaborator sees syntax, metavariables, and expressions, but its work should still produce proof terms that satisfy the kernel. Keep custom tactics local, predictable, and clear about when they fail or leave goals open.

## Further reading

- [Lean reference: Custom Tactics](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Custom-Tactics/)
- [Lean reference: Macros and quotations](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Macros/)
- [Lean reference: Elaborators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/)
- [Lean API: Tactic elaboration state](https://lean-lang.org/doc/api/Lean/Elab/Tactic/Basic.html)
