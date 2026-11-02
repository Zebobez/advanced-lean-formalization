# Chapter 17 — Composing Automation Safely

> **Audience.** This chapter assumes familiarity with ordinary tactic proofs, rewriting, and basic Mathlib automation. It develops a disciplined way to combine automation with explicit proof structure, with particular attention to goal combinators, `solve_by_elim`, and `aesop`.

Automation is most useful when it removes repetitive search while leaving the mathematical structure visible. A proof can be short and still be hard to maintain if it delegates every choice to an opaque search procedure. Conversely, a proof can be explicit without spelling out every routine implication. The goal is to put each decision at the right level: make strategic choices in the proof, and automate predictable local work.

## Learning objectives

By the end of this chapter, you should be able to:

- distinguish deterministic normalization from branching proof search;
- compose tactics with `first`, `<;>`, `all_goals`, and `repeat` without hiding unfinished goals;
- use `solve_by_elim` and `aesop` for suitable logical search;
- limit search by controlling hypotheses, rules, and the shape of the remaining goals;
- turn an exploratory automated proof into a stable, readable library proof.

## 1. Automation belongs at the leaves

Many formal proofs have a recognizable shape. First, the argument chooses a representation, introduces an invariant, performs induction, or divides into cases. Then a number of small goals remain: apply a hypothesis, simplify a constructor equation, discharge an inequality, or prove a local consequence. The strategic work and the routine work are different.

```text
mathematical plan
      │
      ├── choose induction / cases / invariant / representation
      ▼
structured proof skeleton
      │
      ├── apply local search to small leaves
      ▼
kernel-checked proof
```

Automation tends to work best after the proof has exposed the relevant structure. For example, if a theorem says that a conjunction holds, `constructor` reveals two independent obligations. A short `assumption` on each goal communicates exactly what remains:

```lean
example (p q : Prop) (hp : p) : p ∧ p := by
  constructor <;> assumption
```

Here the first tactic makes the proof's logical shape explicit. The `<;>` combinator runs `assumption` on every goal produced by `constructor`. This is a useful boundary: the proof author chooses the connective introduction; automation checks whether the context already contains each component.

Compare that with invoking an unconstrained search tactic before understanding the goal. If the search succeeds, the result may be compact but reveal little about why it succeeds. If it fails, its search behavior may not point to the missing mathematical idea. The strongest default is therefore to expose one layer of structure before asking a tactic to search below it.

This is not a ban on concise proofs. If a proposition is genuinely routine and the automation used is standard in the project, a one-line proof is reasonable. The question is whether the chosen tactic makes an appropriate mathematical commitment or silently chooses among substantially different arguments.

## 2. Goal combinators make scope explicit

Tactic combinators control which goals receive a tactic and how failures are handled. They are small pieces of control flow, and misunderstanding them can make a proof appear complete while leaving obligations behind.

### `first` expresses alternatives

Use `first` when several tactics are alternative ways to solve the same goal:

```lean
example (n : Nat) : n = n := by
  first
  | assumption
  | rfl
```

Lean tries the alternatives in order, backtracking when an alternative fails. For a theorem with an available local proof, `assumption` may work; otherwise reflexivity closes the equality. This is helpful when the alternatives are genuinely interchangeable and the list is short. A long list of unrelated tactics is usually a sign that the proof has not identified the goal's structure.

### `<;>` distributes work over generated goals

The expression `t₁ <;> t₂` runs `t₁` on the current goal, then runs `t₂` on every goal produced by `t₁`. It is especially clear when the second tactic is expected to handle every branch in the same way:

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption
```

If branches require different reasoning, name them with bullets or `case` labels instead. The proof state is then visible in the script:

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq
```

### `all_goals` and `any_goals` encode different contracts

`all_goals tac` requires `tac` to succeed on every goal currently in the state. `any_goals tac` keeps the successful applications and succeeds if at least one goal accepted the tactic. The second form is useful for a deliberately partial cleanup, but it can also conceal which goals remain. Prefer `<;>` when the tactic is specifically the uniform continuation of one preceding tactic; prefer `all_goals` when applying a tactic to the already-present goal list is the point of the code.

The word “all” is literal. If one branch is not handled, `all_goals assumption` fails even if the other branches close. This is often desirable: it prevents a proof from pretending that an incomplete common strategy suffices.

## 3. Repetition is a search strategy

`repeat tac` repeatedly applies a tactic sequence to the main goal while that sequence succeeds. The sequence must eventually fail; otherwise the proof may run indefinitely. In particular, `try tac` succeeds even when `tac` makes no progress, so `repeat (try tac)` can loop forever. This is a useful example of why tactic control flow deserves the same care as recursion in a program.

Use repetition when the operation has a clear decreasing measure. Repeated introductions are an ordinary example:

```lean
example (p q r : Prop) : p → q → r → p := by
  intro hp
  intro hq
  intro hr
  exact hp
```

This explicit version is often clearer than `repeat intro`, but repetition can be suitable when the number of binders is arbitrary or generated. Similarly, `repeat'` recursively visits goals produced by the tactic, whereas `repeat` focuses on repeatedly transforming the main goal. In substantial proofs, use bullets or named cases when branches differ; recursive repetition is harder to inspect when tactics produce a branching tree.

An important safety question is progress. Does each successful iteration reduce the number of leading implications? Does it consume a constructor? Does it simplify a syntactic pattern until no such pattern remains? If no simple measure decreases, use a bounded operation, an explicit list of steps, or a named recursive theorem instead of open-ended repetition.

## 4. Chaining hypotheses with `solve_by_elim`

The `solve_by_elim` tactic repeatedly applies hypotheses and lemmas whose premises can be supplied by the current context or by further search. It is suited to proof trees made mainly from implications and simple elimination rules.

```lean
example (p q r : Prop)
    (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  solve_by_elim
```

The intended proof chain is `hpq hp : q`, followed by `hqr` applied to that result. The tactic saves the author from writing each intermediate implication application. The context and the target remain small enough that the search has a clear job.

When a proof is larger, first state an intermediate fact to constrain the search:

```lean
example (p q r s : Prop)
    (hp : p) (hpq : p → q) (hqr : q → r) (hrs : r → s) : s := by
  have hr : r := by
    solve_by_elim [hpq, hqr]
  exact hrs hr
```

The intermediate target `r` sets a boundary: the search cannot wander through later parts of the proof. Supplying an explicit theorem list also limits which rules are candidates. When `solve_by_elim` finds a proof, inspect whether the search found the intended chain. If that chain is important to the exposition, write the applications explicitly or leave the named intermediate theorem in place.

Avoid using this tactic to discover a missing invariant. If the available hypotheses do not entail the target without a new mathematical construction, the search tactic cannot invent that construction in a useful way. It can only combine the information already exposed.

## 5. `aesop` as extensible logical search

`aesop` is a proof-search tactic supplied with Mathlib. It normalizes goals using configured rules and searches using rules for logical constructors and local assumptions. It can solve many short goals involving conjunctions, disjunctions, existentials, implications, and hypotheses that can be decomposed.

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  aesop
```

For comparison, the proof structure is simple enough to spell out:

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  exact Or.inl hp
```

The explicit proof tells the reader which disjunct is selected. The automated version is useful when the proof is one of many similar logical obligations or when a set of registered domain rules captures a standard argument. It is less informative here because the construction itself is the whole proof.

Aesop's rule system distinguishes normalization, safe rules, and unsafe rules. Normalization aims to simplify a goal without branching. Safe rules are applied eagerly and are not backtracked over; they should preserve provability. Unsafe rules create alternative search paths, allowing backtracking among possible applications. These categories matter when designing custom rule sets: a rule that arbitrarily chooses one branch is unsafe if another branch might be necessary for success.

In routine user proofs, it is usually best to begin with default rules and a tightly prepared goal. Use `aesop?` during exploration to see a suggested proof, but inspect and simplify the suggestion before keeping it. Aesop rule behavior can change with the imported ruleset, so a proof that depends on a large global search environment may be more sensitive to library changes than one that records the key application.

## 6. Constrain search instead of increasing it

When search fails, it is tempting to add more global rules or raise search limits. First diagnose the mismatch between the goal and the available information.

1. Normalize the goal enough to expose its logical constructor.
2. Introduce implications and decompose hypotheses that contain useful structure.
3. Name any mathematical intermediate fact that links the context to the conclusion.
4. Apply automation to the resulting smaller target.

For example, a goal about equality of functions may require `funext`; an arithmetic inequality may require `omega`; an algebraic identity may require `ring`. `aesop` is not a substitute for these domain-specific decision procedures. Nor does a larger search depth replace a missing lemma about monotonicity, injectivity, or an invariant.

There are several ways to focus a search call: supply only relevant lemmas to `solve_by_elim`, use a local theorem to state the target of a search phase, or configure Aesop for a local rule set. Local control is easier to audit than registering a very general rule globally. Global rules affect proofs throughout the import graph and may create search branches in goals their author never considered.

When using Aesop clauses or custom rule registration, document the intended class of goals and why the rule is safe or branching. A rule useful for proving membership in one domain-specific predicate may be inappropriate for unrelated propositions. Keep specialized search in a namespace or module where its assumptions and target are evident.

## 7. Replacing exploratory proof search

Search tactics are excellent discovery tools. They are less automatically suitable as permanent proof scripts. A useful workflow separates discovery from the final argument:

```text
shape the goal → try a search tactic → inspect the result
       │                                │
       └──────── name missing facts ◄───┘
                         │
                         ▼
             keep search local or expose steps
```

If `aesop?`, `exact?`, or another search helper suggests a theorem application, identify the theorem and its arguments. Replace a broad search with a direct `exact` or `apply` when that produces a clear stable proof. If search is the intended public behavior, keep it but state the local facts that make the search predictable.

Do not preserve the first proof merely because it is short. Consider how a maintainer will respond if it breaks: will the goal state indicate which fact is missing, or will a tactic report only that no search path was found? A named helper lemma usually gives better failure localization. The proof can still use automation inside that helper, where the target is narrow.

There is also a kernel-facing reason to keep the result disciplined: tactics generate proof terms, and Lean checks the resulting term. The tactic itself is not trusted as a source of truth. However, a tactic that builds a huge term or repeatedly unfolds a large development can make elaboration and checking slower. Chapter 16's advice about small lemmas applies directly to automation-heavy proofs.

If a tactic's behavior is essential to a public theorem, record the assumptions that support it. A later import may add simp lemmas or search rules, and a Lean or Mathlib update may change the available automation. A small, named helper proof localizes that dependency. When a proof uses a specialized tactic intentionally, mention its role in a nearby comment or theorem name; this helps a maintainer decide whether a failure is mathematical or a change in the tactic environment.

## 8. Common failure modes

### Automation is used before the target is normalized

Rewrite or simplify the expression, or state the needed intermediate result. The tactic may not recognize that two forms encode the same goal.

### One tactic is applied to every branch, but branches differ

Replace `all_goals` or `<;>` with `case` blocks or bullets. A goal split is an opportunity to make the case-specific reasoning explicit.

### A search call becomes slower after adding imports

The environment may contain more rules or instances. Reduce the goal, use a local theorem list, or isolate a specialized rule set. Avoid solving a performance problem by registering broad global rules without understanding their effects.

### Repetition loops or does not make progress

Remove an always-successful tactic such as `try` from the repeated sequence. Identify a decreasing measure, and use a bounded or explicit sequence if the measure is not obvious.

### Aesop proves the proposition by an unexpected route

Inspect the suggested proof or replace the search with explicit constructor and hypothesis applications. Search success is evidence that the target follows from the context, not evidence that the intended argument was formalized.

## 9. Exercises

1. Prove a conjunction from two hypotheses using `constructor <;> assumption`. Then write the proof with bullets. Which version better communicates the intended structure?
2. Use `solve_by_elim` to prove a four-step implication chain. Add a named intermediate theorem and explain how it constrains the search.
3. Take a goal about an existential or disjunction and prove it once with an explicit constructor and once with `aesop`. Identify the choice hidden by automation.
4. Find a proof where `all_goals assumption` fails because one branch needs a different argument. Rewrite it with named cases.
5. Write a tactic sequence using `repeat` that has an obvious decreasing measure, then explain why it terminates. Give an example of a superficially similar sequence that may loop.
6. Use `aesop?` on a small Mathlib goal. Replace the suggested search with explicit lemma applications, and compare the two proof scripts' sensitivity to changes in rule registrations.
7. Design a local intermediate proposition for a goal that `aesop` cannot solve directly. Do not add a global rule; describe what mathematical information the new proposition exposes.

## Summary

Expose the mathematical structure before invoking search. Use `<;>` for uniform work on generated goals, named cases when branches differ, and `repeat` only when progress is clear. Use `solve_by_elim` for short implication chains and `aesop` for routine logical search over an appropriately prepared context. Constrain search locally, inspect exploratory suggestions, and replace broad search with explicit applications when those applications communicate the proof's central choice.

## Further reading

- [Lean reference: The Tactic Language](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/The-Tactic-Language/)
- [Mathlib tactic documentation: `aesop`](https://leanprover-community.github.io/mathlib4_docs/tactics.html)
- [Aesop project documentation](https://github.com/leanprover-community/aesop)
