# Chapter 21 — Dependent Equality and Transport

> **Audience.** This chapter assumes familiarity with ordinary equality rewriting and indexed types. It develops the role of equality as a transport mechanism when types or propositions depend on values, and shows how to keep dependent rewrites understandable.

For an equality `h : a = b`, ordinary rewriting replaces occurrences of `a` with `b`. In dependent code, an occurrence of `a` may appear inside the type of another term. Replacing the index can therefore change the type of that term as well as the expression in which it appears. Lean handles this through transport: equality gives a way to move evidence or data from one fiber of a dependent family to another.

The kernel's equality eliminator is simple, but its consequences appear throughout vectors, subtypes, dependent pairs, indexed inductives, and equivalences. When a rewrite becomes difficult, ask which type depends on the value being rewritten and make the transport visible at that boundary.

## Learning objectives

By the end of this chapter, you should be able to:

- explain transport along an equality using a dependent family;
- choose among `rw`, `subst`, `cases`, and explicit equality elimination;
- recognize casts introduced by dependent rewriting;
- use `congrArg` and `congr` to move equalities through functions;
- simplify proofs by reducing equality hypotheses to reflexivity when appropriate.

## 1. Equality acts on dependent families

Let `P : α → Sort v` be a family of types indexed by values of `α`. If `h : a = b`, then a term of type `P a` can be transported to a term of type `P b`. In Lean's notation, `h ▸ x` expresses this transport:

```lean
example {α : Type} {a b : α}
    (h : a = b) (P : α → Prop) (ha : P a) : P b := by
  exact h ▸ ha
```

The equality does not claim that the proof objects `ha` and `h ▸ ha` have identical types by inspection. It supplies the conversion between the two fibers. The familiar rewrite tactic often performs this transport implicitly, which is why routine equalities do not require users to mention casts.

```text
index:  a ───── h : a = b ─────▶ b
         │                       │
fiber:  P a ─────── h ▸ _ ─────▶ P b
```

The general type of the motive may be `Sort v`, not just `Prop`. Transport applies to data as well as proofs:

```lean
def moveFin {n m : Nat} (h : n = m) (i : Fin n) : Fin m :=
  h ▸ i
```

The term `i` carries a bound in its type. When the bound changes from `n` to `m`, the equality `h` is the information that makes it meaningful to use the same finite index at the new bound. This is a small example of the type changes that arise in vectors, matrices, and syntax indexed by a context.

## 2. Equality elimination reduces transport to reflexivity

The defining principle of equality says that to prove a dependent fact for every equality, it is enough to prove it for reflexivity. In tactic proofs, `cases h` applies this principle to an equality hypothesis. It identifies the two endpoints and replaces the equality with `rfl`.

```lean
example {α : Type} {a b : α}
    (h : a = b) (P : α → Prop) (ha : P a) : P b := by
  cases h
  exact ha
```

After `cases h`, the goal `P b` has become `P a`, and the context no longer needs a separate equality proof. This method is often effective when the equality hypothesis is central and its elimination simplifies several dependent expressions at once.

The term-level operation behind this pattern is equality recursor elimination, frequently presented as substitution or transport. Most users should prefer surface tools such as `rw`, `subst`, and `cases`; writing the recursor explicitly is mainly useful for understanding a difficult type mismatch or defining an abstraction around transport.

The motive controls what is transported. For the example above, the motive is the family `P`. In a dependent function or indexed structure, the motive may include additional arguments. Lean often infers it from the expected type, but when inference cannot determine the intended family, an explicit `show` or type annotation can make the dependency clear.

## 3. Choose the equality tactic that matches the goal

Several tactics can use an equality hypothesis, but their effects differ.

### `rw` rewrites selected occurrences

Use `rw [h]` when you want to replace occurrences in the target or a selected hypothesis. It keeps the equality as a local operation rather than removing one endpoint from the context. Rewriting is the natural choice when both values remain meaningful elsewhere or when only one expression needs to change.

```lean
example (n m : Nat) (h : n = m) : n + 1 = m + 1 := by
  rw [h]
```

The rewrite changes the left side to match the right; reflexivity then closes the goal. In dependent goals, the rewrite may also insert transport terms. Usually those terms are simplified automatically, but they explain why a goal can change more than its printed expression suggests.

### `subst` identifies variables

Use `subst x` when an equality gives a local variable `x` as equal to another expression. The tactic substitutes the expression for that variable throughout the local context and target, then removes the equality. This is useful after case analysis or when the chosen representative should become the only one used in the rest of the proof.

```lean
example (n m : Nat) (h : n = m) : n + 1 = m + 1 := by
  subst m
  rfl
```

Substitution can improve readability when the two names are interchangeable for the remainder of the proof. Avoid using it automatically on every equality: a named relation may carry useful information, and rewriting only one occurrence can better preserve the argument's structure.

### `cases` eliminates the equality

Use `cases h` when identifying the endpoints simplifies dependent hypotheses or indices broadly. It is often the best choice for equality between indices of a family. It can also make the context less readable if many values collapse at once, so examine the resulting case before continuing.

The choice can be summarized as:

```text
need one replacement?             rw [h]
identify a variable globally?     subst x
reduce dependent case to rfl?     cases h
```

The tactics are not interchangeable in every context. Choose the one whose effect matches the proof's next step.

### Direction is part of the transport

If `h : a = b`, then `h ▸ x` moves a term from the fiber over `a` to the fiber over `b`. The symmetric equality moves in the opposite direction. This is easy to lose track of when a rewrite is nested inside several dependent fields.

```lean
def moveFinBack {n m : Nat} (h : n = m) (i : Fin m) : Fin n :=
  h.symm ▸ i
```

Read the type before choosing `h` or `h.symm`: the source type of `i` determines which side of the index equation the transport must start from. If a cast appears in the goal, write its source and destination explicitly on paper. A mistaken orientation often produces an error that looks like a universe or coercion problem, even though the only issue is which endpoint is being transported.

Rewriting can also target a hypothesis whose type depends on the equality. For example, `rw [h] at hx` may change the type of `hx` from `P a` to `P b`. This is convenient when the new form is what the next theorem expects. If other hypotheses depend on `hx`, Lean must update those dependencies as well. When the context becomes difficult to follow, eliminate the equality first and work in the simplified context.

### Naming the family can make inference predictable

The transport notation infers a motive from the expected type. In a large dependent expression, there may be several plausible motives, or the expected type may be hidden behind a coercion. State the family as an explicit function when necessary. Instead of asking Lean to infer the intended relation from a deeply nested term, isolate it in a helper theorem such as “transport an element of `Fin n` to `Fin m` along this equality.” The helper's type records the family and the direction once; clients use that named operation.

This is the same API principle used for ordinary rewriting: expose the stable mathematical operation, and avoid forcing every caller to understand its implementation in terms of recursors. A named transport lemma is especially helpful when a development repeatedly changes the same index, such as a sequence length or a dimension parameter.

## 4. Dependent rewriting can expose a cast

In a nondependent equality, rewriting `n = m` through an expression such as `n + 1` changes only the expression. In a dependent family, changing an index changes the type of a term. Lean must preserve the term's meaning by inserting or reducing a cast.

For example, `Fin n` depends on the natural number `n`. If an equality `h : n = m` is available, a term `i : Fin n` can be transported to `Fin m`. The definition `moveFin` above is this transport written explicitly. When a goal contains a similar change, the editor may display `Eq.rec`, `Eq.ndrec`, `cast`, or a heterogeneous equality after unfolding. These are not unrelated complications; they are the internal form of the equality action.

Before simplifying a cast-heavy goal, identify:

1. the index that changed;
2. the equality relating the old and new indices;
3. the family whose type depends on that index;
4. whether the equality can be eliminated so that the cast reduces to reflexivity.

The fourth step is often the simplest. If the equality is between two variables and no canonical orientation is needed, `cases h` may reduce all transports at once. If the equality is a theorem about arithmetic, rewriting with that theorem may leave a cast whose equality proof is not definitionally `rfl`. Then use a named cast lemma, prove the index equality in the required orientation, or make the transport explicit in a helper theorem.

Do not unfold internal equality recursors as a first response. Their expressions are verbose because they encode dependent substitution generically. Start from the family and index that changed, then work outward.

## 5. Equality under functions and constructors

If `h : a = b` and `f` is a function, congruence gives `f a = f b`. The direct theorem is `congrArg`:

```lean
example {α β : Type} (f : α → β) {a b : α} (h : a = b) :
    f a = f b := by
  exact congrArg f h
```

This pattern generalizes to expressions with several arguments. The `congr` tactic or theorem can reduce equality of applications to equalities of their arguments, often with dependent side conditions. For ordinary arithmetic expressions, `congr` may leave exactly the component equalities that `rw` or `rfl` can handle.

```lean
example (a b c d : Nat) (h₁ : a = c) (h₂ : b = d) :
    a + b = c + d := by
  rw [h₁, h₂]
```

For dependent constructors, congruence may not be enough by itself. If an argument determines the type of a later field, changing the first argument changes what equality of the later arguments means. In that setting, inspect the constructor's dependent fields and use an equality principle formulated for the whole structure or a theorem exposing the needed field relation.

This is one reason bundled maps often provide preservation theorems rather than requiring clients to unfold structure constructors. A library theorem can package the congruence and transport obligations into a stable interface.

## 6. Heterogeneous equality as a diagnostic

Ordinary equality `a = b` requires both terms to have the same type. In a dependent proof, two expressions may be naturally related even though their types differ before transport. Lean's heterogeneous equality `HEq` can express a relation between such terms.

Heterogeneous equality is useful for understanding dependent patterns and some generated theorems, but it should not be the default replacement for ordinary equality. Often the right mathematical statement is an equality after a cast, or an equality of indices that lets a term be transported. Make that intended transport explicit where possible. Reserve `HEq` for APIs or theorem statements whose fields really inhabit different types and where the relation is meaningful without first choosing a cast.

When a `cases` proof leaves a heterogeneous equality, ask whether the surrounding index equality has been used. A dependent constructor may produce hypotheses that look heterogeneous before the index equation is substituted. Eliminating that equation can turn them into ordinary equality. Conversely, forcing a cast too early can make the expression more verbose than the original heterogeneous relation.

## 7. Common failure modes

### Rewriting changes a hypothesis type unexpectedly

Inspect the declaration's dependencies. The rewritten variable may occur in the type of another hypothesis, not just its proof term. Use `cases` or `subst` if identification of the indices is the intended next step.

### A term does not have the expected indexed type

Find the exact index in its type and the equality that relates it to the target index. Transport the term along that equality or prove the index equality in the appropriate direction.

### A cast does not simplify

The cast may use a non-reflexive equality proof, or the expected family may not be definitionally the same as the one Lean inferred. Expose the motive, use an appropriate cast theorem, or eliminate a simpler equality earlier.

### `subst` makes a proof harder to read

Use a local rewrite instead if the equality is needed in a specific expression but both names remain mathematically useful.

### The goal displays `Eq.rec` or `Eq.ndrec`

Do not treat that display as the mathematical problem. Identify the original index, its equality, and the dependent family. Then reduce the equality to reflexivity or use the library theorem designed for that transport.

## 8. A transport workflow

When a dependent rewrite fails, use the following sequence:

1. Write down the source and target types of the term being rewritten.
2. Identify the index or value on which those types depend.
3. Orient the equality so the source fiber moves to the target fiber.
4. Try `rw`, `subst`, or `cases` according to the desired scope.
5. If a cast remains, expose it in a small helper lemma and prove the corresponding transport statement.
6. Return to the main theorem using the helper lemma's stable interface.

This method prevents a long theorem from becoming a debugging exercise in recursor syntax. A small lemma such as `moveFin` names the direction and family of a transport, and later proofs can use it without repeating the equality elimination.

## 9. Exercises

1. Prove the dependent predicate example using both `cases h` and `rw [h]`. Compare the resulting proof states.
2. Define a transport function for `Fin n` along an equality of bounds, then state a theorem describing what happens when the equality is reflexivity.
3. Use `subst` to prove an equality of expressions. Rewrite the proof using a single `rw`; explain which style better preserves the role of both variables.
4. Prove that applying a function preserves equality with `congrArg`. Generalize the result to a two-argument function and identify the two required equalities.
5. Find a theorem involving a subtype or indexed family whose proof contains a cast. Identify the index equality and the family being transported.
6. Give an example where a dependent constructor's second field changes type with its first field. Explain why ordinary congruence alone does not describe the field equality.
7. Read a goal containing `Eq.ndrec` and rewrite its type as a source family, an equality of indices, and a transported term. Do not unfold the recursor in the final proof unless the public API requires it.

## Summary

Equality in a dependent family transports terms and proofs between types indexed by equal values. Use `rw` for selected replacements, `subst` to identify a variable throughout the context, and `cases` to reduce an equality-dependent situation to reflexivity. `congrArg` moves equality through functions, while dependent constructors may require explicit transport or a specialized theorem. When casts appear, reason from the family and index before inspecting the internal recursor.

## Further reading

- [Lean reference: Propositional Equality](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Propositional-Equality/)
- [Lean API: Equality and transport](https://lean-lang.org/doc/api/Init/Core.html)
