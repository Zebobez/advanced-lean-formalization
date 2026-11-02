# Chapter 12 — Finite Types and Combinatorial Proofs

> **Audience.** This chapter assumes familiarity with functions, finite sets, and basic induction. It focuses on choosing between explicit finite sets and finite types, proving cardinality statements, and organizing combinatorial arguments around enumeration and reindexing.

Finite mathematics in Lean has two complementary representations. A `Finset α` is an explicit finite collection of elements of `α`. A `Fintype α` is evidence that every element of the type `α` can be enumerated. The distinction affects how a theorem is stated: are we counting one selected finite subset, or are we summing or quantifying over every element of a finite type?

This chapter uses both representations. It develops cardinality proofs by disjoint union, finite sums by induction, and finite types as domains for exhaustive reasoning. The examples show how typeclass instances supply enumeration and why membership and cardinality often belong in the theorem statement rather than in a manually constructed list.

## Learning objectives

By the end of the chapter, you should be able to:

- distinguish `Finset α` from a type equipped with `[Fintype α]`;
- use `Finset.card` and `Fintype.card` appropriately;
- prove cardinality facts by disjoint decomposition;
- prove a finite-sum identity by induction on `Finset.range`;
- use `Fin n` and `Finset.univ` as canonical finite index domains;
- plan a combinatorial proof by choosing a useful enumeration or partition.

The examples are in namespace `Chapter12`.

## 1. Two ways to represent finite collections

A `Finset α` is a finite collection of values of type `α`, with duplicates removed. For many operations such as union and insertion, Lean needs a decision procedure for equality on `α`; this appears as a `[DecidableEq α]` instance. The cardinality is written `s.card`:

```lean
namespace Chapter12

example {α : Type _} [DecidableEq α] (a : α) : ({a} : Finset α).card = 1 := by
  simp
```

The value `s : Finset α` describes one particular finite subset. Membership in it is a proposition `x ∈ s`, and operations such as union, intersection, difference, and insertion change that subset.

A `Fintype α`, by contrast, provides an enumeration of all values of `α`. The canonical finite collection of all elements is `Finset.univ`, and `Fintype.card α` counts the elements in the type:

```lean
example (n : Nat) : Fintype.card (Fin n) = n := by
  simp
```

The type `Fin n` is the standard domain for exactly `n` choices. Each value contains a natural number below `n`, and the type's cardinality theorem connects the bound to enumeration.

These representations fit together:

```text
finite type α with [Fintype α]
             │
             └── all elements ──▶ Finset.univ : Finset α

selected finite subset ────────▶ s : Finset α
```

Use a `Finset` when the theorem is about a selected collection. Use a `Fintype` when the whole type is finite and the argument ranges over every element. A theorem can use both: a `Finset` may select a subset of a `Fintype` domain.

## 2. Cardinality of a disjoint union

If two finite sets are disjoint, their union contains each element of either set exactly once. The cardinality is therefore the sum of the cardinalities:

```lean
example {α : Type _} [DecidableEq α] (s t : Finset α)
    (h : Disjoint s t) : (s ∪ t).card = s.card + t.card := by
  exact Finset.card_union_of_disjoint h
```

The theorem's hypothesis is essential. If an element occurs in both sets, adding the two cardinalities counts it twice. Without disjointness, the general union formula must account for the intersection.

This is a useful proof pattern: describe a finite object as a union of pieces, prove that the pieces are disjoint, and apply a cardinality theorem. The argument separates the combinatorial decomposition from the arithmetic that combines the sizes.

The same pattern applies to a finite set partitioned into even and odd elements, a graph's vertices split into two classes, or a collection split by whether a property holds. Before using a disjoint-union theorem, prove both facts that make the partition valid: the pieces cover the original collection, and no element belongs to two pieces.

### Inclusion-exclusion as a diagnostic

For overlapping sets, the correction is the intersection. The identity

```text
card(s ∪ t) + card(s ∩ t) = card(s) + card(t)
```

expresses inclusion-exclusion. A useful habit is to test a proposed counting formula on an element in the overlap. If it is counted twice on one side and once on the other, an intersection term or disjointness assumption is missing.

When formalizing a decomposition, write the set identity and disjointness theorem before the cardinality calculation. This keeps membership logic from being buried inside arithmetic tactics.

## 3. Induction on a finite set

Many finite-set arguments follow an induction principle with two cases: the empty set and insertion of a new element. The insertion case includes a proof that the inserted element is not already present. That condition is precisely what makes the cardinality increase by one and prevents duplicate counting.

The shape is:

```text
empty set: establish the base count

insert a s, with a ∉ s:
    use the induction result for s
    account for the new element a
```

This induction is appropriate when the statement is genuinely about all finite sets and its behavior is stable under adding one fresh element. If a finite set is defined by a range, induction on the range bound may be more natural. Choose the induction variable that mirrors how the collection is constructed.

For a finset proof, the element-not-in-set condition is not an annoying side goal; it is the semantic guarantee that insertion really adds one new value. If the proof has no use for this condition, reconsider whether the theorem should be stated in a way that accounts for existing membership.

## 4. Finite sums by induction on a range

The finite sum over a range is a standard combinatorial object. Here is a proof that the sum of the first `n` positive odd numbers is `n²`:

```lean
open scoped BigOperators

theorem sum_odd_numbers (n : Nat) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring
```

The induction mirrors the construction of `Finset.range (n + 1)`: the new range contains the old range plus the new endpoint. The library equation `Finset.sum_range_succ` exposes that decomposition. The induction hypothesis handles the old terms, and `ring` verifies the resulting polynomial identity.

The proof is a small instance of a broadly useful method:

1. Choose a finite collection whose recursive structure matches the induction.
2. Rewrite the sum using the collection's equation.
3. Apply the induction hypothesis to the smaller collection.
4. Finish the algebraic identity with a specialized tactic.

The finite sum is not evaluated element by element by the proof script. The induction and equation lemma establish a general identity for every bound `n`.

The same principle applies to sums over products and subtypes. First choose a domain whose elements correspond directly to the objects being counted, then use the product or subtype structure to split the sum. If two domains are related by a bijection, reindexing is usually clearer than constructing a term-by-term correspondence between their underlying lists. The finite API provides sum and product theorems that preserve this structure.

For sums over an arbitrary `Finset`, the corresponding induction principle is empty/insertion. The base case simplifies to zero; the insertion case reduces to the summand at the new element plus the previous sum. The proof then depends on the algebraic operation being summed, such as addition in a commutative monoid.

## 5. Finite types and exhaustive reasoning

When a type has an instance `[Fintype α]`, Lean knows it is finite, but the proofs need not manually list its elements. The typeclass instance supplies the enumeration to generic theorems. For example, cardinality is invariant under equivalence:

```lean
example {α β : Type _} [Fintype α] [Fintype β] (e : α ≃ β) :
    Fintype.card α = Fintype.card β := by
  exact Fintype.card_congr e
```

This theorem is useful when the finite type has a convenient alternative representation. Instead of proving its cardinality from scratch, build an equivalence with a type whose size is already known.

For a finite type, a universal statement can often be proved by cases over all elements, but unrestricted case splitting is not always the clearest proof. Prefer a theorem that reasons generically about `Fintype`, `Finset.univ`, or cardinality when the result should work for every finite type. Reserve explicit enumeration for small domains where each case is mathematically meaningful.

This distinction helps avoid brittle proofs. A proof that names all elements of `Fin 5` may stop reflecting the theorem if the bound changes. A proof by an equivalence or cardinality theorem expresses the property of the whole finite family.

## 6. Reindexing and double counting

Many combinatorial identities compare two ways of enumerating the same objects. A bijection is the formal bridge: it proves that the two finite types have the same cardinality. When summands are also preserved by the bijection, reindexing transfers a finite sum from one domain to another.

The mathematical plan is:

```text
objects described by representation A
             │ bijection
             ▼
objects described by representation B
```

For a counting theorem, the bijection alone is enough. For a sum identity, additionally show that corresponding objects contribute equal summands. This proof structure is often clearer than manipulating two finite sums directly.

Double counting is the same idea applied to a set of incidences. Count the pairs in a finite relation by fixing the first coordinate, then count them again by fixing the second coordinate. In Lean, choose a finite type or finset of pairs, define the relevant fibers, and prove each decomposition covers the same collection. The difficult step is usually the bijection or partition, not the final arithmetic.

When a counting proof becomes tangled, name the finite set of objects being counted. State its two decompositions as separate lemmas. Then use cardinality or sum-reindexing theorems to translate each decomposition into an equation. This gives the proof a stable intermediate object and makes overcounting errors easier to detect.

## 7. Fibers and the pigeonhole principle

For a function between finite types, the fiber over `y` is the set of inputs mapped to `y`. Fibers partition the domain: every input belongs to exactly one fiber. Counting the domain by fibers is a standard route to pigeonhole arguments and average-size results.

The informal proof plan is:

1. Define the set of inputs mapping to each output.
2. Prove that distinct fibers are disjoint.
3. Prove that the union of all fibers is the whole domain.
4. Sum the fiber cardinalities.

If a map from a larger finite type to a smaller one were injective, every fiber would have at most one member, so the domain could not have more elements than the codomain. If every fiber has exactly `k` members, the domain size is `k` times the codomain size when the map is surjective. These are cardinality arguments, but their core is a partition of the domain.

Lean's finite-type cardinality theorems can often prove the final inequality once injectivity or surjectivity is bundled as a function property. For a detailed combinatorial theorem, an explicit finite set of pairs may make the fiber argument easier to formalize: each pair records an input and its output, and the two projections give the two counting directions.

The proof should not begin by manipulating cardinal numbers blindly. First establish the structural facts about the map: every input has one output, every claimed output has a preimage, and any assumed injectivity prevents two different inputs from occupying the same fiber. These facts say what the fibers look like. Cardinality theorems then turn them into inequalities or equalities between natural numbers.

## 8. Membership, decidability, and classical reasoning

Operations on `Finset α` sometimes need `[DecidableEq α]` to determine whether two values are equal and to remove duplicates. A predicate-based subset may need a `DecidablePred` instance to decide membership computationally. In theorem proofs, a local `classical` command can supply classical decision procedures when executable computation is not required.

Use classical reasoning when it simplifies a proof that is purely propositional. If the finite set is meant to be computed, prefer explicit decision procedures and computational data. The distinction is similar to the one between a theorem that merely exists and a program that must produce an answer.

Cardinality proofs should generally use the API's membership and disjointness theorems rather than opening the underlying multiset representation of a finset. The abstraction boundary ensures duplicate-freeness remains handled by the library. Reason about membership, union, insertion, and disjointness; use `card` lemmas to translate that structure into natural-number arithmetic.

## 9. Common failure modes

### A cardinality sum double counts elements

Prove disjointness before applying the disjoint-union formula. If the sets overlap, use an inclusion-exclusion statement or partition the collection more carefully.

### A finite set is confused with a finite type

Use `Finset α` for a selected collection and `[Fintype α]` for an enumeration of all elements of a type. `Finset.univ` connects the two when needed.

### Insertion does not add one element

The inserted value may already belong to the finset. Establish nonmembership or use a theorem whose conclusion accounts for the existing element.

### A sum proof unfolds too much

Use the range or insertion equation for the finite sum, then apply the induction hypothesis. Avoid expanding the entire sum into individual terms.

### Explicit enumeration obscures a general theorem

Use an equivalence, cardinality theorem, or `Fintype` result when the claim is invariant across finite representations. Enumerate cases only when the cases themselves matter.

## 10. Exercises

1. Prove that the cardinality of a singleton finset is one, and identify the equality-decision information needed to form it.
2. Prove the disjoint-union cardinality identity from `Finset.card_union_of_disjoint` for your own finite sets.
3. Use `Finset.card_union_eq_card_add_card` to characterize when a union has cardinality equal to the sum of the individual cardinalities.
4. Adapt `sum_odd_numbers` to prove a formula for the sum of the first `n` natural numbers. State the algebraic identity needed in the successor step.
5. Construct an equivalence between two finite types and use `Fintype.card_congr` to transfer a cardinality result.
6. Describe a double-counting proof for a relation on two finite types. Name the set of incidences and state the two possible decompositions.
7. Find a proof that explicitly lists elements of a finite type. Rewrite it using an abstract finite-type or cardinality theorem if the result is independent of the enumeration.

## Summary

`Finset α` represents a selected finite collection; `[Fintype α]` represents a finite type with an enumeration. Use `Finset.card` for selected subsets and `Fintype.card` for whole types. Disjoint decompositions turn cardinality proofs into sums, while range and insertion equations expose the structure needed for induction over finite sums. Equivalences support reindexing and double counting. Keep membership and duplicate-freeness inside the finset API, and make disjointness or nonmembership assumptions explicit when they justify a counting step.

## Further reading

- [Mathlib: Finset cardinality](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Card.html)
- [Mathlib: Fintype cardinality](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Card.html)
- [Mathlib: Finite sums and products](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/Finset/Basic.html)
- [Mathematics in Lean: Sets and Finite Sets](https://leanprover-community.github.io/mathematics_in_lean/)

end Chapter12
