# Chapter 22 — Classical Reasoning and Computability

> **Audience.** This chapter assumes experience with ordinary theorem proofs, existential statements, and executable definitions. It explains where classical reasoning enters Lean, why extracting data from a proposition can require noncomputable choice, and how to preserve executable content when a development needs it.

Lean supports classical mathematics, but its underlying logic also supports constructive proofs. The distinction matters most when a declaration computes data. A theorem can use excluded middle without producing a program. A definition that selects an element from an existence proof may depend on choice and therefore cannot be compiled as an algorithm. Formalizations become clearer when the proof-level and data-level roles are separated explicitly.

This chapter is about design, not a ban on classical reasoning. Mathlib uses classical principles throughout ordinary mathematics. The practical question is whether the result is intended only as a theorem or also as executable data, and whether the development needs to expose its axiom dependencies.

## Learning objectives

By the end of the chapter, you should be able to:

- use classical reasoning locally in propositions;
- distinguish existential proof from extraction of a witness as data;
- explain when a definition must be marked `noncomputable`;
- avoid accidentally asking `decide` to evaluate a classical instance;
- inspect and document the axioms on which a declaration depends.

## 1. Constructive and classical goals

Constructive logic asks a proof of an existential statement to provide a witness together with evidence that the witness works. A proof of `∃ x, P x` can be built from a value `x` and a proof of `P x`. Classical reasoning allows additional principles, including excluded middle, that do not supply a computational witness for an arbitrary proposition.

Lean's `Classical` namespace contains the standard classical principles. The tactic `classical` locally enables classical decidability for proof work:

```lean
theorem doubleNegation (p : Prop) : ¬¬p → p := by
  classical
  intro h
  by_contra hp
  exact h hp
```

The theorem says that the double negation of `p` implies `p`. Its proof uses classical reasoning. This is appropriate for a theorem in ordinary classical mathematics. The tactic does not change the proposition or insert an unverified proof; it makes classical instances available while elaborating the proof.

If the statement admits a direct constructive proof, prefer that proof when constructivity is part of the intended result. Otherwise, use classical reasoning where it simplifies the mathematics. Do not assume that every theorem must be constructive merely because Lean's core logic allows constructive proofs.

Scope classical instances to the proof that needs them. A local `classical` command in a theorem proof makes the dependency easy to see and avoids changing the behavior of later definitions in the file. Opening the `Classical` namespace more broadly can also make propositions decidable, but a data-producing `if` may then depend on a noncomputable decider. Narrow scope is especially valuable in modules that mix theorem proving with executable code.

## 2. Propositions may express existence without data

In a constructive proof of an existential proposition, the proof construction provides a witness. Lean can use that witness in further proposition-level reasoning by cases. But `Exists` lives in `Prop`, and elimination restrictions prevent an arbitrary existential proof from serving as a general program that returns a value in `Type`. There is a type-theoretic boundary between establishing that some `x` exists and defining executable code that returns an `x`.

Consider an existence theorem:

```lean
theorem has_witness {α : Type} {P : α → Prop} (h : ∃ x, P x) :
    ∃ x, P x := h
```

This theorem simply preserves a proof. It does not define a computational function from arbitrary propositions to values. To return the witness itself as data, one must choose how to extract it.

```lean
universe u

noncomputable def selectWitness {α : Type u} {P : α → Prop}
    (h : ∃ x, P x) : α :=
  Classical.choose h

theorem selectWitness_spec {α : Type u} {P : α → Prop}
    (h : ∃ x, P x) : P (selectWitness h) :=
  Classical.choose_spec h
```

`Classical.choose` returns a selected witness, and `choose_spec` proves that it satisfies the property. The definition is marked `noncomputable` because classical choice does not provide an algorithm for finding the value. The accompanying theorem is an ordinary logical guarantee about the selected value.

This pattern is useful for mathematics: once existence has been proved, downstream arguments can name a witness. It is not suitable when the result must run as a program. In that case, define a search procedure and prove that the procedure returns a correct witness whenever one exists.

The distinction is not that Lean forgets the witness during a proof. Tactics such as `rcases h with ⟨x, hx⟩` can expose it while proving another proposition. The restriction concerns using proofs in `Prop` to compute unrestricted data. The logic keeps proof elimination compatible with proof irrelevance and computation; `Classical.choose` crosses that boundary by using a noncomputable principle.

## 3. `Nonempty` and `Inhabited` encode different information

The distinction appears in two familiar type classes. `Nonempty α` is a proposition asserting that some value of `α` exists. It does not expose the value to computation. `Inhabited α` contains a chosen default value, which can be used computationally as `default`.

This difference affects API design. A theorem that only needs existence should usually require `Nonempty α`; it should not demand a globally chosen default. A function that must return a fallback value can require `[Inhabited α]`. If the only available premise is `Nonempty α`, converting it into an element uses classical choice and makes the result noncomputable.

The stronger-looking data class is not always better. Requiring `[Inhabited α]` may force callers to choose an arbitrary default that the theorem never uses. Conversely, using `Nonempty α` in a return type may be insufficient for an executable algorithm that must produce an actual value. State the requirement that matches the operation.

For subtypes, an existence proof can be turned into a proof that the subtype is nonempty. Extracting a specific subtype value still requires a choice principle unless the proof was built constructively and its witness is available in the term. Prefer preserving the witness from a constructive proof rather than erasing it and selecting it later.

This gives a useful API test. Ask whether a client needs (a) the proposition that a value exists, (b) permission to assume a value temporarily in a proof, or (c) an actual value returned by a function. These require different interfaces. `∃ x, P x` serves the first. A `Nonempty` assumption can serve the second. A returned subtype or an algorithmic result serves the third. Changing one into another is not merely notation; it may require choice or an explicit search procedure.

## 4. `noncomputable` marks a code-generation boundary

The `noncomputable` modifier tells Lean that a definition uses a logical construction for which executable code should not be generated. Typical sources are `Classical.choice`, classical `Decidable` instances, and other axioms that produce data without an algorithm.

```lean
noncomputable def arbitraryElement (α : Type) [Nonempty α] : α :=
  Classical.choice ‹Nonempty α›
```

The body is logically meaningful: from nonemptiness, classical choice supplies an element. But code generation cannot turn the proof of `Nonempty α` into a concrete runtime value. Marking the definition prevents a misleading expectation that it can be evaluated as ordinary executable code.

A `noncomputable section` can group several such declarations when the same boundary applies. Keep its scope narrow. A broad section can accidentally mark later helper definitions noncomputable and obscure which declaration introduced the dependency.

The modifier is about computational execution, not theorem validity. A theorem may use classical choice in its proof without needing to return data. A `noncomputable def` can still be used in mathematical statements and proofs; it simply cannot be compiled as an executable program in the ordinary way. Use `#eval` or code-generation errors as a clue about computational dependencies, and inspect the definition chain when an unexpected declaration becomes noncomputable.

Noncomputability also propagates through definitions that depend on a noncomputable value. If a computational API begins with a chosen representative, then every later definition that evaluates or returns that representative inherits the boundary. The right repair is often not to add `noncomputable` farther downstream, but to decide whether the initial choice belongs in the executable interface. A finite search procedure, a canonical representative theorem, or an explicit user-supplied witness may restore computation.

## 5. Classical decidability and `decide`

The tactic `decide` computes by reducing a `Decidable` instance. Classical reasoning can make every proposition decidable in the logical sense, but the resulting instance is not an algorithm that evaluates to `isTrue` or `isFalse` for arbitrary propositions. This is the connection to Chapter 19: adding a classical instance can make a proposition typeclass-decidable while removing the computational path that `decide` needs.

For example, equality of arbitrary functions is not generally computably decidable. A classical context can prove that either two functions are equal or they are not, but it cannot inspect infinitely many inputs to determine which case holds. Use extensionality and mathematical hypotheses for a function equality theorem; do not expect `decide` to evaluate it.

When a decision tactic unexpectedly stops reducing, inspect the active instance. Did `classical` introduce a noncomputable decider? Is the proposition closed? Does its `Decidable` instance reduce on the inputs provided? Choose a proof method suited to the statement rather than adding more computation options.

This matters for `if` expressions as well. Lean elaborates a proposition-valued condition using a `Decidable` instance. In a proof, a classical instance can justify reasoning by cases. In executable code, the condition must be decided computationally. If a data-producing `if` depends on an arbitrary proposition, the definition will need a noncomputable boundary unless the API supplies an actual decision procedure.

## 6. Keep algorithms constructive when output matters

Suppose a finite list is known to contain an element satisfying a predicate. An executable selection function should search the list and return either an element with proof or a failure result. Its specification can then connect the output to the mathematical existence statement.

```text
finite input + decidable test
          │ executable search
          ▼
option of witness and proof
          │ correctness theorem
          ▼
specification about existence
```

This design preserves useful computation. The search algorithm can be evaluated; its correctness theorem can be used abstractly; and clients that care only about existence need not inspect implementation details.

For infinite domains, the situation is different. A proof that a witness exists may rely on compactness, choice, or a nonconstructive existence theorem. There may be no algorithm that finds a witness from the proof alone. Mark the chosen witness definition noncomputable, or keep the theorem existential and avoid pretending it is an executable search procedure.

If executable output is a project requirement, decide early which constructions must be computable. This affects the theorem statements and interfaces: a constructive theorem can provide data directly, while a classical theorem may provide only a proposition. Rebuilding the interface at the end can require substantial refactoring.

## 7. Axiom auditing

Lean's kernel checks proof terms, but a declaration may depend on axioms or other foundational principles. `#print axioms name` lists the axioms on which a theorem or definition depends. This is useful for understanding a trust boundary, not only for checking whether `sorry` remains.

Classical choice is standard in Mathlib's classical mathematical development. Its appearance in an axiom listing is not automatically a defect. The audit question is whether the dependency is expected for the intended result. A theorem about a finite algorithm may be expected to avoid choice; a theorem using arbitrary selections or classical existence may reasonably depend on it.

Audit at the declaration that matters. A low-level lemma might be constructive while a higher-level theorem imports classical choice through a library result. Conversely, a theorem may use `classical` to simplify proof search but its final type may not require noncomputable data. `#print axioms` reveals the transitive dependency rather than relying on the visual appearance of the proof script.

For a public API, consider recording this information where users make computational decisions. A theorem can remain mathematically useful even when it depends on `Classical.choice`; an executable function cannot silently inherit the same expectation of runtime evaluation. Separate those declarations and document which one carries the computational guarantee.

When reporting a result externally, state the relevant assumptions accurately. “Kernel checked” means Lean verified the proof term under its logic and imported axioms; it does not mean the theorem is independent of every axiom. Chapter 19's native computation adds its own visible axiom. The two cases have different sources and should not be conflated.

## 8. Common failure modes

### A theorem is marked noncomputable unnecessarily

Check whether the classical feature occurs in the theorem's proof only or in a data-producing definition. Theorem proofs generally do not require executable code generation. Narrow the modifier to the definition that selects data.

### A witness can no longer be computed

The proof may have erased the constructive witness into an existential proposition. Preserve the witness in the return value or define a subtype result containing both the data and its property.

### `decide` fails after adding `classical`

Classical decidability proves that a decision exists but does not provide a reducible algorithm. Use a computational instance, a theorem, or a reflective tactic that matches the proposition.

### A function needs an arbitrary fallback value

Require `[Inhabited α]` if a canonical default is genuinely part of the API. If only existence is known, either return an optional result or state that the selection is noncomputable.

### An axiom listing is mistaken for a proof failure

Read which axiom appears and why. Classical choice and native computation are expected in some developments. The listing is a dependency report; compare it with the project's stated foundational or execution requirements.

## 9. Exercises

1. Prove double-negation elimination for a proposition using `classical`. Explain which step uses excluded middle.
2. Define a function that selects a witness from `∃ x, P x` with `Classical.choose`, then prove its specification. Mark only the required declaration noncomputable.
3. Compare `Nonempty α` and `[Inhabited α]` in two APIs: one that proves existence and one that must return a default value.
4. Use `#print axioms` on a theorem proved classically and a theorem using a standard constructive argument. Explain the transitive dependencies.
5. Design an executable search over a finite list that returns an optional witness. State a theorem relating successful output to the predicate.
6. Give an example where `classical` helps prove a proposition but should not appear in an executable definition. Explain the difference between their outputs.
7. Review a noncomputable definition in a library. Identify whether its noncomputability comes from choice, a classical decider, or another declaration.

## Summary

Classical reasoning is appropriate for ordinary mathematics, but classical existence does not necessarily provide executable data. Use `classical` locally in proposition proofs, use `Classical.choose` when a selected witness is needed, and mark data-producing definitions that depend on choice as `noncomputable`. Distinguish `Nonempty` from `Inhabited`, preserve constructive witnesses when outputs matter, and use `#print axioms` to understand a result's dependencies. A classical `Decidable` instance is not the same as an algorithm that `decide` can evaluate.

## Further reading

- [Lean: Axioms and Computation](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/)
- [Lean reference: Basic Classes and Decidability](https://lean-lang.org/doc/reference/latest/Type-Classes/Basic-Classes/)
- [Lean API: Classical reasoning support](https://lean-lang.org/doc/api/Init/Classical.html)
- [Lean FAQ: Is Lean's logic classical?](https://lean-lang.org/faq/)
