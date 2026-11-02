# Chapter 25 — Linear Maps and Submodules

> **Audience.** This chapter assumes familiarity with modules, linear maps, and subspaces. It focuses on Mathlib's bundled linear-map and submodule interfaces, especially kernels, ranges, images, preimages, and the universal properties behind them.

Linear algebra formalization becomes much more reusable when functions carry the laws that define them. A linear map packages additivity and compatibility with scalar multiplication. A submodule packages an additive subgroup closed under scalars. Their bundled operations let proofs talk about kernels, ranges, images, and quotients without rebuilding closure arguments every time.

The key proof-engineering change is to move between three levels deliberately: element membership, the submodule order, and the linear map itself. Use membership lemmas to open a local algebraic argument, order lemmas to compare whole subspaces, and bundled map theorems when a property follows abstractly from linearity.

## Learning objectives

By the end of this chapter, you should be able to:

- read and use the type of a bundled linear map;
- choose between element-level and submodule-level reasoning;
- treat kernels and ranges as submodules with stable interfaces;
- use `map` and `comap` to push forward and pull back subspaces;
- organize proofs around universal properties rather than carrier sets.

## 1. A linear map carries its algebraic laws

For modules over a ring `R`, a linear map has type `M →ₗ[R] N`. It is a bundled map that preserves addition and scalar multiplication. The typeclass assumptions on `M` and `N` determine the relevant additive and module structures; the map itself records the preservation laws.

```lean
example {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (x y : M) :
    f (x + y) = f x + f y := by
  simp
```

The simplifier uses the map's `map_add` theorem. Scalar multiplication is handled in the same way. The purpose of bundling is that downstream theorems can use these facts generically, regardless of how the map was defined.

An unbundled function `M → N` may still be preferable for a temporary construction, especially before its preservation properties are known. Once a theorem repeatedly assumes additivity and scalar compatibility, the bundled type reduces repeated hypotheses and gives library search a standard structure to find.

The notation can be semilinear when the scalar rings differ. A semilinear map includes a ring homomorphism that translates scalars. Unless the scalar action itself is central to the argument, use the standard notation and let the type state the relationship rather than expanding all the fields.

## 2. Submodules are bundled subsets

A submodule `E : Submodule R M` is a subset of `M` closed under zero, addition, and scalar multiplication. It is also an ordered object: `E ≤ F` means every element of `E` belongs to `F`. The lattice operations express intersections, spans, and generated subspaces.

Membership is the right interface for local algebra. The order is the right interface for statements about entire subspaces. For example, a proof that a kernel lies below a submodule may eventually need to show `x ∈ E`; once a generic inclusion theorem is available, the proof can remain at the submodule level.

Mathlib submodules coerce to sets and to types of elements satisfying the invariant. This is convenient, but the coercion boundary should stay visible. If `x : E`, then `(x : M)` is its underlying vector. A membership proof `hx : x ∈ E` and a subtype element `x : E` encode related information in different forms. Use the form expected by the theorem rather than adding coercions mechanically.

This follows the general pattern from Chapter 5: a subobject can be represented as a predicate and as a subtype. The bundled `Submodule` carries both the carrier and closure laws, while its coercions let ordinary set and element reasoning remain available.

## 3. Kernels and ranges are submodules

The kernel of `f : M →ₗ[R] N` is the submodule of inputs mapped to zero. Its range is the submodule of outputs attained by the map. These are not merely sets: closure under the module operations follows from linearity and is packaged in their types.

```lean
example {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (x : M) :
    x ∈ LinearMap.ker f ↔ f x = 0 := by
  simp
```

The membership lemma is a common point of entry from a submodule goal to an element equation. Conversely, a range-membership goal typically becomes an existence statement: an output belongs to the range exactly when it is the image of some input. Use the library's membership simp lemmas rather than unfolding the carrier of the range.

The kernel captures failure of injectivity. If `f` is injective, its kernel is the bottom submodule. If the kernel is bottom, equality of two images can be reduced to equality of inputs by applying linearity to their difference. Mathlib provides standard equivalences for these facts; search for kernel and injectivity lemmas before reproving the argument from `map_add` and `map_smul`.

The range captures surjectivity. A map is surjective precisely when its range is top. This formulation composes naturally with submodule operations and finite-dimensional arguments. If a proof uses only that a particular vector is in the range, stay with membership and a witness; if it uses surjectivity globally, use the submodule equality or a bundled equivalence.

Kernels also behave predictably under composition. For `f : M →ₗ[R] N` and `g : N →ₗ[R] P`, an input lies in the kernel of `g.comp f` exactly when its image under `f` lies in the kernel of `g`. At the submodule level, this says that the composite kernel is a comap. The element proof is one line of function evaluation; the submodule theorem records a reusable structural law. This is a good example of when both levels are useful: membership explains the fact, while the bundled identity lets a later theorem apply it without repeating the calculation.

Similarly, the range of a composite is constrained by the range of its outer map and, under suitable assumptions, by the image of the original range. Surjectivity and injectivity hypotheses determine whether those inclusions become equalities. Read the hypotheses on range theorems carefully; a statement for an arbitrary composite may provide only an inclusion, while a surjective or injective map gives stronger simplification.

## 4. Push submodules forward and pull them back

Given a linear map `f : M →ₗ[R] N`, Mathlib provides `Submodule.map f E`, the image of a submodule `E : Submodule R M`, and `Submodule.comap f F`, the preimage of `F : Submodule R N`.

```text
E ⊆ M   ── f ──▶   f(E) ⊆ N
                    ▲
                    │ comap: all inputs whose image lies in F
F ⊆ N   ◀──────────┘
```

The image is constructed as a submodule because linear maps preserve the operations required for closure. The preimage is a submodule because the inverse image of a submodule under a linear map is closed under zero, addition, and scalar multiplication.

These constructions satisfy an order equivalence:

\[
  \operatorname{map}(f,E) \le F
  \quad\Longleftrightarrow\quad
  E \le \operatorname{comap}(f,F).
\]

This is the linear-algebra instance of the general Galois connection from Chapter 23. It turns a proof about the image of every vector in `E` into a proof that `E` lies in the preimage of `F`. After establishing the relationship once, use the library theorem `Submodule.map_le_iff_le_comap` rather than repeating the elementwise argument.

The kernel is the preimage of bottom, and the range is the image of top. These identities reveal how much of linear algebra is the interaction of order on submodules with maps between modules. They also explain why `map` and `comap` are central API operations rather than incidental notation.

## 5. Prove subspace statements at the right level

Many proofs become noisy because they move between elements and submodules too often. A useful pattern is to open membership only for the part that needs element-level reasoning:

1. state the inclusion between submodules;
2. introduce an arbitrary element of the source;
3. use its membership and the algebraic hypotheses;
4. close membership in the target;
5. return to the submodule inclusion.

For a goal about `Submodule.map f E ≤ F`, the element-level claim is that every image `f x`, for `x ∈ E`, lies in `F`. For `E ≤ Submodule.comap f F`, the claim is that every `x ∈ E` satisfies `f x ∈ F`. The Galois equivalence identifies these as two forms of the same property.

When the target is bottom, simplify membership to an equation with zero. When the target is top, membership is immediate. When the target is an intersection, prove both component memberships. The lattice structure lets these common forms reduce with `simp` once the element-level facts have been named.

For sums of submodules, the lattice supremum is the span of the union of the two carriers, not generally their set-theoretic union. The union of two submodules need not be closed under addition. The infimum, by contrast, is their intersection. This is a recurring reason to phrase subspace statements using `⊔` and `⊓`: the notation invokes the correct closed construction and lets lattice lemmas handle it abstractly.

The same caution applies to arbitrary indexed families. The supremum of a family of submodules is the span of all their carriers; membership may require a finite linear combination drawn from the family. If the theorem only needs each member to lie below a fixed submodule, use the universal property of `iSup` instead of unpacking that span. This avoids inventing finite witnesses that the goal never uses.

Avoid unfolding the definition of `Submodule.map` to a span of an image unless the proof genuinely concerns generating sets. The span formulation is mathematically valid but usually introduces linear combinations and witnesses that the higher-level map API already hides.

## 6. Factor maps through submodules

Suppose a linear map sends every vector in `E` into `F`. One can restrict its domain to the subtype `E`, or codomain-restrict it to `F`. These constructions encode a map between subspaces without losing the fact that the values satisfy the target condition.

This is a dependent typing issue as well as an algebraic one. A codomain-restricted function returns a subtype element, so each output comes with a proof of membership in `F`. The underlying linear map to `N` is recovered by coercion. A theorem about the underlying vector may need `Subtype.val` or an extensionality lemma to remove the subtype wrapper.

For repeated use, name the restricted map. That keeps the membership proof near the construction and gives later theorems a standard object to compose. For a one-off proof, it may be simpler to establish the image inclusion directly and avoid introducing a new map.

Restrictions also clarify the difference between an injective map into a subspace and a surjective map onto it. A codomain restriction changes the codomain to a subtype and stores the proof that every output belongs there; it does not by itself prove surjectivity. A range restriction can be surjective onto the range, while injectivity remains a separate property of the original map. Keep these properties separate in the API so that later equivalences require exactly the hypotheses the mathematics supplies.

The kernel and range of these restricted maps often have concise descriptions in terms of intersections and comaps. Such theorems are preferable to expanding subtype values and proving equality of their underlying functions by hand. They preserve the algebraic meaning while letting Lean manage coercions and proof fields.

## 7. Quotient spaces and universal properties

Submodules connect to quotient modules. If a linear map has a submodule in its kernel, it can often factor through the quotient by that submodule. The quotient identifies vectors whose difference lies in the chosen submodule. Rather than constructing a representative-dependent map, use the quotient's universal property: define a map on representatives, prove it respects the equivalence relation, and obtain the induced map on equivalence classes.

This is the same proof design used for quotients in Chapter 9, now enriched with linear structure. The factor map's well-definedness is the key proof obligation; its linearity should then follow from the induced operations or from the quotient map API. Avoid choosing representatives noncomputably unless a computational representative is actually needed.

For a map `f`, the first isomorphism theorem relates the quotient by its kernel to its range. In Mathlib, use the provided linear equivalence rather than rebuilding the correspondence. The theorem exposes the conceptual decomposition of a map while insulating downstream proofs from the implementation of quotient representatives.

## 8. Common failure modes

### A plain function has no `map_add` theorem

If a proof repeatedly assumes linearity, change the function's type to `M →ₗ[R] N` or package its laws in a helper structure. A function type alone does not carry algebraic preservation.

### Membership is hidden behind a coercion

Write the carrier explicitly or use `change` to reveal the expected membership statement. Distinguish a vector in the ambient type from an element of the subtype.

### An image proof unfolds into a span calculation

Try `Submodule.map`, `Submodule.comap`, and their order lemmas first. Unfold spans only when generators or linear combinations are the mathematical content.

### Kernel membership is proved from scratch

Use the kernel membership simp theorem to convert to `f x = 0`. Use injectivity/kernel equivalence theorems for global conclusions.

### A quotient map depends on a representative

Prove invariance under the quotient relation and use the quotient lift. The universal property is designed to remove the representative choice from client proofs.

## 9. Exercises

1. Use `simp` to prove the linearity equations for a bundled map, then inspect the theorem names used by the simplifier.
2. Prove the kernel membership characterization by rewriting `LinearMap.ker` as a comap of bottom. Compare this with the simp proof.
3. Show that `Submodule.map f E ≤ F` and `E ≤ Submodule.comap f F` express the same condition. State the elementwise argument in both directions.
4. For an injective linear map, prove that the kernel is bottom. Then find and use the generic theorem that provides this equivalence directly.
5. Construct a codomain restriction from a map whose range lies in a submodule. Explain how the subtype proof is used in the linear map structure.
6. State the factorization problem for a map that vanishes on a submodule. Identify the quotient relation and the proof needed for well-definedness.
7. Find Mathlib's first isomorphism theorem for linear maps and explain which objects play the roles of quotient by kernel and range.

## 10. Formalized exercise patterns

These solutions show how kernel membership, the map–comap adjunction, and the injectivity criterion fit together. The algebraic details remain available when needed, while the standard submodule API handles statements about entire subspaces.

### The kernel as a comap

```lean
theorem exercise_25_2_kernel_is_comap
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) :
    LinearMap.ker f = Submodule.comap f ⊥ := by
  rfl

theorem exercise_25_2_kernel_membership
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (x : M) :
    x ∈ LinearMap.ker f ↔ f x = 0 := by
  change f x ∈ (⊥ : Submodule R N) ↔ f x = 0
  simp
```

The kernel is definitionally the comap of the zero submodule. The second proof exposes that definition and then reduces membership in bottom to equality with zero.

### Map–comap adjunction

```lean
theorem exercise_25_3_map_le_iff_comap
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (E : Submodule R M) (F : Submodule R N) :
    Submodule.map f E ≤ F ↔ E ≤ Submodule.comap f F := by
  simpa using
    (Submodule.map_le_iff_le_comap
      (f := (f : M →ₛₗ[RingHom.id R] N)) (p := E) (q := F))
```

The forward implication says every image of an element of `E` lies in `F`; the reverse implication says every element of `E` maps into `F`. Mathlib packages this equivalence so later proofs can change sides without opening membership witnesses.

### Injectivity and a trivial kernel

```lean
theorem exercise_25_4_injective_iff_kernel_eq_bot
    {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Injective f ↔ LinearMap.ker f = ⊥ := by
  simpa using
    (LinearMap.ker_eq_bot
      (f := (f : M →ₛₗ[RingHom.id R] N))).symm
```

This is the global version of kernel membership: an injective map has no nonzero input in its kernel, and a trivial kernel forces equal outputs to come from equal inputs.

## Summary

Use `M →ₗ[R] N` for maps whose linearity is part of the interface and `Submodule R M` for closed subsets of a module. Kernels and ranges are submodules; `map` and `comap` push and pull subspaces and form an order adjunction. Open membership for local algebra, but keep whole-subspace statements at the lattice level. For quotient factorizations, use the universal property and the library's induced linear equivalences instead of choosing representatives by hand.

## Further reading

- [Mathematics in Lean: Linear Algebra](https://leanprover-community.github.io/mathematics_in_lean/C10_Linear_Algebra.html)
- [Mathlib: Linear map definitions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Defs.html)
- [Mathlib: Kernels of linear maps](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Ker.html)
- [Mathlib: Mapping and comapping submodules](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Map.html)
