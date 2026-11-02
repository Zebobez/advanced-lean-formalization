# Chapter 14 — Finding and Reusing Library Theorems

> **Audience.** This chapter assumes you already use Mathlib and can read theorem statements. It develops a practical search workflow: turn the proof goal into a library query, inspect candidates, and reuse the theorem at the right abstraction level.

Large formalizations are rarely built from first principles. The library already contains many definitions, instances, lemmas, and bundled constructions that match common mathematical patterns. Finding the right declaration is a proof skill in its own right. Good search begins with understanding the target and ends with a theorem whose statement says exactly what the proof needs.

Automation can suggest candidates, but it cannot replace reading them. A theorem with the right name may require stronger assumptions than expected, use a different orientation, or be stated for a more general structure. Learn to inspect the candidate's type and context before choosing it.

## Learning objectives

By the end of the chapter, you should be able to:

- use `#check` and `#print` to inspect declarations;
- use `exact?`, `apply?`, `rw?`, and `simp?` as interactive search tools;
- search by theorem shape, namespace, and mathematical vocabulary;
- adapt a candidate theorem by supplying arguments, rewriting, or changing the goal;
- distinguish a theorem's public API from its implementation details;
- turn a successful search result into a readable, stable proof.

## 1. Start from the proof state

Before searching the library, read the target and local context. Identify:

- the type of each expression;
- the relation in the goal (`=`, `≤`, membership, equivalence, and so on);
- which assumptions are available;
- which part of the conclusion remains to be shown;
- whether the goal asks for a general fact or just one rewrite step.

For example, a goal about `f (x * y)` suggests a structure-preservation theorem if `f` is a homomorphism. A goal about equality of functions suggests extensionality. A goal about a numerical inequality suggests an order theorem or decision procedure. If the proof state is not understood, a search result may appear relevant while solving the wrong problem.

Write the expected theorem in ordinary mathematical language. Then identify its logical shape: an equality, implication, equivalence, universal statement, or data constructor. That shape narrows both the names and the search tactics to try.

## 2. Inspect a candidate with `#check`

The `#check` command elaborates an expression and reports its type. Use it to confirm a theorem's signature before applying it:

```lean
#check Nat.add_comm
#check MonoidHom.map_mul
```

The output reveals implicit arguments, typeclass requirements, and the orientation of the theorem. It can also show whether an identifier is the declaration you intended or a similarly named result from a different namespace.

If a theorem is a global constant and you want to inspect its definition or proof term, use `#print`:

```lean
#print Nat.add_comm
```

For proof development, the type is usually more important than the implementation. Start with `#check`; use `#print` when you need to understand a definition's transparency or inspect how a result was constructed.

Commands are especially helpful when elaboration is ambiguous. A fully qualified name such as `Nat.add_comm` removes uncertainty about namespace resolution. If the theorem has implicit type or structure arguments, the expected target may infer them; otherwise, pass named arguments explicitly.

The generated type is often more informative than a search-result summary. It shows whether the theorem is polymorphic, which instances it needs, and whether a hypothesis is implicit or explicit. A statement that looks general in prose may require commutativity, finiteness, decidable equality, or a nonzero condition. `#check` exposes those obligations before the theorem is inserted into a larger proof.

## 3. Search the goal with `exact?` and `apply?`

The `exact?` tactic searches for a theorem that closes the current goal, resolving straightforward side conditions from the local context when possible. The `apply?` tactic searches for a theorem whose conclusion can refine the goal and may leave smaller conditions to prove.

For example, a transitivity goal can be presented to search:

```lean
example (i j k : Nat) (h₁ : i < j) (h₂ : j < k) : i < k := by
  exact?
```

Lean may suggest a term such as `Nat.lt_trans h₁ h₂`. The important output is the theorem and its arguments. Replace the search tactic with the suggested proof after checking that it expresses the intended reasoning.

These tactics are interactive aids. Their results depend on the imported environment and available search procedures, so they should not be treated as a stable proof API. A named theorem application is easier for a reader to understand and is less sensitive to changes in the search environment.

Use `apply?` when you recognize the theorem's conclusion but still need to discover the lemma that provides it. Use `exact?` when the goal is already in its final shape and a direct proof may exist. If a search tactic produces a candidate with an unfamiliar assumption, read that assumption; it may reveal a missing hypothesis in the theorem statement.

## 4. Search for rewrites with `rw?` and `simp?`

When the goal is nearly correct but has a term in the wrong form, `rw?` searches for an equality or equivalence that can rewrite it. When simplification closes a goal, `simp?` reports a narrower `simp only` invocation that suffices.

These tools answer different questions:

- `rw?`: which theorem can transform this expression?
- `simp?`: which simplification lemmas are sufficient for this proof?

For example, if `simp` closes a small goal, `simp?` can suggest the specific equation used. This is useful when the global simp set is large and you want to understand which theorem is doing the work. The resulting `simp only` form can be a helpful record, though it may be too brittle if the proof should tolerate harmless changes in simp attributes.

As with `exact?`, `rw?` is a search command, not necessarily the final proof. Use the suggested theorem explicitly when it clarifies the intended rewrite. If the rewrite changes the wrong occurrence, combine the theorem with targeted rewriting from Chapter 10.

## 5. Search by type shape and mathematical vocabulary

Theorem names are often predictable once you recognize the mathematical structure. A theorem preserving a multiplication under a homomorphism is likely to involve `map_mul`; a result about an inverse may involve `inv`; a theorem about equality of functions may be in an `ext` namespace or carry an `_ext` suffix.

Useful search paths include:

1. Search the local project or Mathlib source for a distinctive term in the goal.
2. Search the generated Mathlib documentation by declaration name or type.
3. Use a type-pattern search service such as Loogle when the theorem's name is unknown.
4. Ask `exact?`, `apply?`, or `rw?` from the actual goal state.
5. Inspect a likely namespace with `#check` on the candidate declaration.

Search by the most distinctive part of the statement. Searching for `map_mul` is more useful than searching for “homomorphism theorem,” and searching for `Finset.card_union` is more useful than “finite set formula.” A distinctive type or operation reduces unrelated results.

If a theorem's name is unknown, work outward from the notation in the goal. Resolve overloaded operations with `#check`, then search the underlying type or operation. For example, finite-sum notation elaborates to `Finset.sum`; searching for the operation is more productive than guessing a notation-specific theorem name.

Evaluate search results by their assumptions, not only by whether they close the current goal. A theorem that succeeds because a strong typeclass, a local classical instance, or an unintended coercion happens to fit may be less reusable than a nearby theorem with a better interface. Record the candidate's mathematical prerequisites before adopting it.

Documentation pages are especially useful for declarations that have a family of related lemmas. The page often links to the source module, neighboring declarations, instances, and attributes. Follow those links when one theorem solves the immediate goal but you expect to reuse the construction in several related results.

Namespaces are mathematical organization. If a theorem concerns `Finset`, look in `Finset`; if it concerns a homomorphism, inspect the map's namespace and the generic `map_*` results. The fully qualified name in the editor or documentation gives a reliable starting point.

### Worked search workflow

Suppose the target contains `f (a * b)` and the context contains `f : M →* N`. The shape points to a multiplication-preservation theorem. Search the name `map_mul`, then inspect the candidate:

```lean
#check MonoidHom.map_mul
```

The statement confirms that it accepts a bundled monoid homomorphism and two source elements. The proof is then explicit:

```lean
example {M N : Type _} [Monoid M] [Monoid N]
    (f : M →* N) (a b : M) : f (a * b) = f a * f b := by
  exact map_mul f a b
```

This is a repeatable search method: identify the operation, search its law, inspect the declaration's type, and apply it with the objects already present in the context. If the target were about a ring homomorphism preserving addition, the same shape would lead to `map_add` instead.

## 6. Adapt theorem statements deliberately

A candidate theorem may not match the goal syntactically even when it is mathematically right. The mismatch may be due to:

- reversed equality orientation;
- implicit arguments that need to be specified;
- a stronger theorem with extra hypotheses;
- a result stated for a typeclass rather than a concrete structure;
- a coercion or notation difference;
- a missing rewrite that would put the target into the theorem's form.

Before abandoning the candidate, try a small adaptation: reverse the equality with `←`, rewrite the goal into a normal form, provide named arguments, or use `change` to state a definitionally equivalent target. If the theorem requires a hypothesis that the mathematics cannot supply, it is not the right theorem.

Prefer the most general theorem that fits the argument without adding needless complexity. A theorem for every monoid is usually more reusable than one for natural numbers, but the concrete theorem may be clearer when the proof itself is specifically about naturals. Abstraction is valuable when it helps the proof, not as an end in itself.

## 7. Read the declaration's surrounding API

Finding one theorem often reveals neighboring declarations that complete the interface. If `#check` shows a `map_mul` lemma, inspect the same namespace for `map_one`, `map_pow`, composition, identity, extensionality, injectivity, and range results. A well-designed API groups related operations and laws.

Look at attributes as well as names. A theorem marked `[simp]` may already be available to `simp`. A theorem marked `[ext]` may be discovered by `ext`. A typeclass instance may let a generic theorem apply without manually supplying the structure. Knowing the role of the declaration prevents duplicate helper lemmas in your project.

When using a typeclass-generic theorem, inspect its assumptions. If a theorem requests `Monoid`, the proof may be reusable for a group or ring because those structures inherit monoid behavior. If it requests `CommMonoid`, the commutativity assumption is mathematically essential to the result. Avoid adding a stronger structure than the theorem needs.

## 8. Turn discovery into maintainable proof code

Once a search finds the right theorem, rewrite the proof in a style that records the mathematical reason. A search tactic can close a goal quickly, but leaving it in a library theorem makes the proof depend on future search behavior. Prefer an explicit application:

```lean
example (i j k : Nat) (h₁ : i < j) (h₂ : j < k) : i < k := by
  exact Nat.lt_trans h₁ h₂
```

If the result is a simplification fact, decide whether ordinary `simp` is appropriate or whether a named theorem should be applied explicitly. If a direct proof is longer than the statement deserves, a concise automation call is reasonable. The objective is not to eliminate tactics; it is to make the proof's dependency clear.

Capture a useful repeated result in a local lemma when it gives a clearer name or a stronger reusable statement. Do not create a duplicate of a library theorem just to rename it unless the local name expresses a meaningful domain concept. Thin aliases make search harder and can diverge from the original API.

Finally, check the version context. Mathlib declarations and theorem names can evolve. A generated documentation page may describe a newer release than the project's `lake-manifest.json`. When a candidate is missing, inspect the dependency version and search the source that the project actually imports.

## 9. Common failure modes

### A search tactic is left in final proof code

Use it to discover a theorem, then replace it with the suggested declaration or an explanatory tactic. Search behavior may change as the environment changes.

### The theorem's name looks right but its type does not

Read the full signature with `#check`. Confirm source and target types, assumptions, direction, and typeclass requirements.

### Search begins with a vague phrase

Extract a distinctive operation, type, or relation from the goal. Search by mathematical shape rather than a general topic word.

### A concrete theorem is used when a generic one is available

Check whether the proof only needs a weaker structure such as a monoid or additive group. The generic result may simplify both assumptions and reuse.

### A newer online result is unavailable locally

Compare the online docs with the project's pinned Mathlib version. Search the version actually imported before changing dependencies.

### The discovered theorem has an unwanted side condition

Verify the side condition mathematically. If it is missing from the context, find a theorem whose assumptions are true or prove the condition separately; do not hide it with an unjustified rewrite.

## 10. Exercises

1. Use `#check` to inspect the type of a theorem you already know, then record its implicit arguments and typeclass assumptions.
2. Use `exact?` on a simple transitivity goal and replace its suggestion with an explicit theorem application.
3. Use `apply?` on a goal whose proof requires an intermediate theorem. Read any remaining obligations it leaves.
4. Use `simp?` after `simp` closes a goal. Explain which rewrite rules were necessary and which were unnecessary.
5. Search Mathlib for a homomorphism theorem matching a goal about the image of an operation. Use `#check` to verify its signature.
6. Find two theorems with similar names in different namespaces. Explain how their statements differ and which one your goal needs.
7. Search a current Mathlib docs page for a theorem, then compare its name and assumptions with the version pinned by a Lean project.

## Summary

Read the proof state before searching. Use `#check` to inspect theorem types, `#print` for definitions, and `exact?`, `apply?`, `rw?`, and `simp?` as interactive discovery tools. Search by type shape, operation, and namespace. Adapt a promising theorem with explicit arguments or a small rewrite, then replace search tactics with readable proof code. The library is most useful when its existing abstractions and API laws are understood rather than copied blindly.

## Further reading

- [Lean reference: Checking Types and Printing Definitions](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/)
- [Lean reference: Library Search tactics](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference)
- [Mathlib generated API documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Loogle theorem search](https://loogle.lean-lang.org/)

