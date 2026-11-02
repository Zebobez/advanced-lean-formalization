# Chapter 26 — Bases and Finite-Dimensional Arguments

> **Audience.** This chapter assumes familiarity with vector spaces, linear independence, and dimension. It explains how Mathlib represents bases through finitely supported coordinates, how to use basis extensionality, and how finite-dimensional assumptions interact with finite index types and `finrank`.

A basis is often introduced as a family of linearly independent vectors that spans the space. Mathlib packages the same information as a linear equivalence from the space to a coordinate model. This representation makes coordinate extraction, uniqueness, reindexing, and transport across linear equivalences available through a common API.

The implementation choice has practical consequences. Infinite bases require finite-support coordinates rather than arbitrary functions. Finite-dimensional spaces permit a more familiar function-valued coordinate model. A robust formalization stays with the basis abstraction until the proof genuinely needs coordinates or a finite sum.

## Learning objectives

By the end of the chapter, you should be able to:

- read a basis as a linear equivalence with a coordinate space;
- use `Finsupp` to understand coordinates for an arbitrary index type;
- prove maps or vectors equal by checking basis values or coordinates;
- construct and reindex bases through standard APIs;
- use finite-dimensionality and `finrank` without confusing finite index data with arbitrary bases.

## 1. A basis is an equivalence with a coordinate model

For a basis `b : Basis ι K V`, Mathlib provides a linear equivalence

```lean
b.repr : V ≃ₗ[K] (ι →₀ K)
```

The notation `ι →₀ K` is the type of finitely supported functions from the index type `ι` to the field `K`. Each vector has finitely many nonzero coordinates, even when the basis is infinite. This is the algebraic direct sum of copies of the field, not the unrestricted function space `ι → K`.

The inverse equivalence reconstructs a vector from its finite list of nonzero coefficients. Thus a basis supplies both directions: take coordinates, or form the finite linear combination represented by those coordinates.

```text
vector x ∈ V ── b.repr ──▶ finitely supported coordinates ι →₀ K
     ▲                                  │
     └──────────── b.repr.symm ─────────┘
```

The basis vectors are written `b i`. The `i`th coordinate of `x` is `(b.repr x) i`, and the coordinate functional is bundled as `b.coord i`. The representation is useful even when no explicit scalar coordinates are needed: since `b.repr` is an equivalence, it can transfer equalities, linear maps, and algebraic properties between `V` and the coordinate model.

## 2. Why coordinates have finite support

An arbitrary function `ι → K` may be nonzero at infinitely many indices. Such a function would describe an infinite formal linear combination, which is not defined in an ordinary algebraic vector space. The `Finsupp` representation enforces the finite-combination rule in the type.

For a finite index type, every function has finite support, so `ι →₀ K` is equivalent to `ι → K`. Mathlib offers `Basis.equivFun` for this finite-index version. It is often more convenient for matrix and tuple calculations, but it requires a finite index type and is therefore not the general definition of basis coordinates.

This distinction matters when the index type is not visibly finite. If the goal includes a finite basis assumption, Lean may infer the needed `Finite` instance from `FiniteDimensional` or an explicit hypothesis. If the index type is truly arbitrary, do not coerce a `Finsupp` to a total function and then reason as if infinite sums were available.

The support of `b.repr x` identifies exactly which basis vectors occur in the expansion of `x`. Library lemmas state that `x` lies in the span of the basis vectors indexed by this support. This gives a finite witness for each vector without choosing a global enumeration of an infinite basis.

## 3. Use basis APIs instead of manual linear combinations

The basis API exposes several useful constructions:

- `Basis.mk` builds a basis from a linearly independent family that spans the space;
- `Basis.constr` builds a linear map by prescribing its values on basis vectors;
- `Basis.reindex` transports a basis along an equivalence of index types;
- `Basis.map` transports a basis along a linear equivalence of vector spaces;
- `Basis.repr` and `Basis.coord` provide coordinates and coordinate functionals.

These operations correspond to mathematical universal properties. A linear map out of a free vector space is determined by its values on a basis. A reindexing changes the labels but not the vectors. A linear equivalence changes the ambient space while preserving the basis structure.

If an existing theorem establishes linear independence and spanning, use the basis constructor rather than creating an ad hoc structure containing the two proofs. The standard `Basis` type immediately gives coordinate maps, extensionality, and compatibility with other linear constructions.

For an infinite index type, a prescribed family may have repeated vectors; this immediately prevents linear independence unless the indexing type itself distinguishes the repeated positions in a way compatible with independence. Families are used rather than sets precisely because repeated elements and their dependence remain visible in the type.

## 4. Equality can be checked on a basis

Two linear maps out of a space are equal if they agree on every basis vector. In Mathlib, the type is named `Module.Basis`; after `open Module`, the theorem `Basis.ext` packages this principle:

```lean
open Module

example {K V W : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W]
    {ι : Type*} (b : Basis ι K V)
    (f g : V →ₗ[K] W)
    (h : ∀ i, f (b i) = g (b i)) :
    f = g := by
  exact b.ext h
```

This proof is stronger than extensionality on all vectors: the linear structure ensures that values on basis vectors determine the map. It is often the shortest route when proving that two constructions are the same linear transformation.

Elements can also be compared through their coordinates. If every coordinate of `x` agrees with the corresponding coordinate of `y`, then `x = y`. The proof uses injectivity of the coordinate equivalence. This is useful when the original vectors are complicated but their expansions are simple.

Choose the comparison method based on the data already available. If formulas are simple on generators, use map extensionality on a basis. If coordinates are already computed, use coordinate extensionality. Do not prove equality by unfolding both vectors into long sums when the basis API has a theorem matching the statement.

The universal property behind this extensionality also gives a construction principle. To define a linear map out of `V`, prescribe an output for each basis vector and extend linearly. `Basis.constr` performs this extension, and basis extensionality proves it is the only such map. This is often cleaner than defining the map by coordinates and separately showing it respects every vector-space operation.

For vectors, a related equality principle says that matching all coordinates suffices. This can be much simpler than proving equality by induction on a finite sum, because the equivalence `b.repr` turns the question into extensional equality of finitely supported functions. Use the simp lemmas for `Finsupp` evaluation and single-support functions to normalize the coordinate side.

## 5. Change basis through equivalences

Reindexing a basis does not change its span or linear independence. Given an equivalence between index types, `Basis.reindex` assigns the same basis vectors new labels. Given a linear equivalence `e : V ≃ₗ[K] W`, `Basis.map` sends each basis vector through `e` to produce a basis of `W`.

The coordinate transformation is similarly abstract. A linear equivalence induces a relationship between the two representation maps, and library lemmas describe how coordinates change. This is more stable than writing a coordinate transformation matrix and proving by hand that it is invertible.

For a finite-dimensional space, two bases may have different index types but equal finite cardinality. Reindexing along an equivalence of those index types makes them comparable. If the goal is equality of the basis families themselves, first align the index types; if the goal is equality of their spans or dimensions, an index-level equivalence may be unnecessary.

Avoid equating bases that use different index types directly. Their vectors may describe the same structure, but their types record distinct labels. Use a reindexing equivalence, compare their `repr` maps, or formulate the theorem in terms of the underlying subspaces.

## 6. Finite-dimensionality and basis indices

For a vector space over a division ring, `FiniteDimensional K V` states that the space is spanned by a finite family, equivalently that it has a finite basis. The typeclass lets Mathlib infer many finiteness consequences without asking the user to choose a particular basis in every theorem.

`Module.finrank K V` is the natural-number-valued dimension used for finite-dimensional results. The general `Module.rank K V` is cardinal-valued and can represent infinite dimension. A crucial caveat is that `finrank` is defined as zero for some infinite-rank modules. Use it as dimension only under the appropriate finite-dimensional assumptions; otherwise use `Module.rank` or state finite-dimensionality.

An arbitrary basis may be indexed by a type that is not visibly `Fin n`. A finite-dimensional assumption can imply that its index type is finite, but a theorem that needs explicit enumeration may still require `Fintype ι` or a conversion to a `Fin`-indexed basis. Keep this distinction clear:

```text
FiniteDimensional K V     existence of some finite basis
Finite ι                  the current basis index type is finite
Fintype ι                 a chosen enumeration is available computationally
```

`Finite` is a proposition that a type has finitely many elements. `Fintype` packages an enumeration. The latter supports finite sums and explicit case splits. If the proof only needs a cardinality theorem, avoid choosing an enumeration unnecessarily.

## 7. Constructing a basis from finite data

In finite-dimensional arguments, a common pattern is to show that a family of `n` vectors is linearly independent and that `n` equals the dimension. Then the family forms a basis. Mathlib has constructors for this pattern, so proofs should aim to provide the two conceptual inputs rather than manually building inverse coordinate maps.

The reverse approach is also useful: from a basis indexed by a finite type, derive finite-dimensionality, then use dimension lemmas to compare subspaces, kernels, and ranges. The exact theorem may be stated using `Fintype.card`, `finrank`, or a finite set of vectors. Inspect the hypotheses carefully; many dimension statements require a division ring or a field, while the more general basis API works over semirings.

When an argument involves a submodule, remember that it is itself a module through the subtype. A finite-dimensional ambient space induces finite-dimensionality of its submodules and quotients through standard instances and theorems. This can simplify downstream proofs, but it may also make typeclass search infer a basis index in a way that is not computationally explicit.

If a proof needs a concrete basis for computation, choose an explicit one such as a standard basis on a function space. If it needs only an existence theorem, use the abstract finite-dimensional interface and avoid exposing a noncomputable choice of basis.

## 8. Matrices as coordinates of linear maps

Once finite bases are fixed on `V` and `W`, a linear map `V →ₗ[K] W` can be represented by a matrix. Its entries are the coordinates of the images of basis vectors. The matrix is not the map itself; it depends on the chosen bases. Changing either basis changes the coordinate matrix while preserving the underlying linear transformation.

This separation suggests a clean proof strategy:

1. prove the map statement abstractly using linearity;
2. choose bases only when a coordinate computation is needed;
3. use the coordinate equivalences to translate to matrices;
4. use matrix algebra for the finite calculation;
5. transport the result back through the same bases.

If the theorem is invariant under change of basis, avoid committing to a particular matrix too early. A coordinate-free statement is typically more reusable and often has a shorter proof through `LinearEquiv` or `Basis.repr`.

Conversely, when the theorem is explicitly about determinants, rank, or a concrete matrix representation, coordinates are the natural language. The point is not to avoid matrices but to isolate basis dependence so it does not leak into unrelated statements.

The change-of-basis matrix is the coordinate representation of the identity map viewed through two coordinate equivalences. This viewpoint explains why it is invertible: it represents a composition of linear equivalences. Instead of proving a matrix is invertible by expanding determinants, one can often establish the corresponding linear equivalence first and then transfer it to coordinates. For determinant computations, the explicit matrix may still be the right object, but its invertibility then rests on a reusable structural fact.

## 9. Common failure modes

### Coordinates have the wrong function type

For arbitrary bases, coordinates are in `ι →₀ K`, not `ι → K`. Use `Basis.equivFun` only when the index type is finite.

### A map equality is proved on every vector

If both maps are linear, use `Basis.ext` and prove equality only on basis vectors.

### Two bases cannot be compared because their index types differ

Reindex one basis along an equivalence, or state the result using spans or dimensions instead of basis equality.

### `finrank` gives zero unexpectedly

The space may not be known to be finite-dimensional. Add the mathematically required finite-dimensional assumption, or use cardinal-valued `rank` for a statement that includes infinite dimension.

### A noncomputable basis appears in an executable definition

Supply an explicit basis with computational data, or keep the theorem abstract. Existence of a basis does not provide an executable choice of one.

### A matrix proof depends on arbitrary basis choices

Isolate the coordinate step using `Basis.repr` or a `LinearEquiv`, and state the main result invariantly when possible.

## 10. Exercises

1. Use `Basis.ext` to prove two linear maps equal from agreement on all basis vectors.
2. Explain why `Basis.repr` has codomain `ι →₀ K` for an infinite basis. Give a vector whose coordinate function has finite but nonempty support.
3. For finite `ι`, compare `Basis.repr` with `Basis.equivFun`. What additional structure makes the ordinary function model possible?
4. Construct a basis from a linearly independent family whose cardinality equals `finrank`. Find the relevant Mathlib constructor and state its assumptions.
5. Use a linear equivalence to map a basis from `V` to `W`, then identify the theorem that relates the resulting representation maps.
6. Explain why `Module.finrank` alone does not prove finite-dimensionality for a general module. Contrast it with `Module.rank`.
7. For a linear map between finite-dimensional spaces, describe how a choice of bases yields a matrix. Identify which parts of the formalization depend on those choices.

## Summary

A basis identifies a module with finitely supported coordinate functions. Use `Basis.repr` for general index types and `Basis.equivFun` when the index is finite. Prove equality of linear maps by checking basis vectors, and compare vectors through their coordinates when that is the simpler representation. Use `FiniteDimensional` and `finrank` under the appropriate field or division-ring assumptions; switch to cardinal-valued rank for infinite-dimensional statements. Keep basis choices abstract unless a concrete coordinate calculation is the point of the theorem.

## Further reading

- [Mathematics in Lean: Linear Algebra](https://leanprover-community.github.io/mathematics_in_lean/C10_Linear_Algebra.html)
- [Mathlib: Basis definitions and coordinate maps](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Basis/Defs.html)
- [Mathlib: Basis constructions and extensionality](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Basis/Basic.html)
- [Mathlib: Finite-dimensional vector spaces](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional/Defs.html)
- [Mathlib: `finrank`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html)
