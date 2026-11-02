# Chapter 29 — Polynomial Rings and Evaluation

> **Audience.** This chapter assumes familiarity with rings, homomorphisms, and finite sums. It develops the interfaces used to represent polynomials, evaluate them in other algebras, and connect roots with divisibility and degree.

Polynomial proofs in Lean are most effective when they distinguish three different tasks: manipulating a polynomial as an algebraic expression, evaluating it at an element, and reasoning about its roots as a finite collection. Mathlib provides separate interfaces for each task. The formalization becomes fragile when one unfolds polynomial coefficients or conflates evaluation with substitution into a particular coefficient ring.

This chapter builds on the bundled-map and linear-algebra discussions earlier in the book. It emphasizes the roles of `Polynomial R`, `eval`, `eval₂`, `aeval`, and the root APIs, and shows how their assumptions guide proof design.

## Learning objectives

By the end of the chapter, you should be able to:

- read a polynomial as a finitely supported coefficient function without unfolding that representation in routine proofs;
- choose between `eval`, `eval₂`, and `aeval` based on the source and target rings;
- use evaluation homomorphisms and simplification to prove root facts;
- distinguish root predicates, root sets, and root multisets;
- track domain and nonzero assumptions in root-counting theorems.

## 1. A polynomial is a finite coefficient family

For a semiring `R`, `Polynomial R` represents formal expressions

\[
  a_0 + a_1 X + \cdots + a_n X^n
\]

with coefficients in `R`. Internally, this is a finitely supported function from exponents in `ℕ` to coefficients. The finite-support representation means that every polynomial has only finitely many nonzero coefficients, even though its coefficient function is defined at every natural number.

The public API hides this representation behind coefficient operations, degree operations, and algebraic constructors. Use `p.coeff n` to inspect a coefficient. Use `C a` for the constant polynomial, `X` for the variable, and `monomial n a` for a single term. These names describe the mathematical object directly and compose with the polynomial ring operations.

```lean
example {R : Type*} [Semiring R] (a : R) :
    Polynomial.C a * Polynomial.X = Polynomial.monomial 1 a := by
  exact Polynomial.C_mul_X_eq_monomial
```

The exact theorem used in a calculation is usually supplied by simplification lemmas for `C`, `X`, and `monomial`. If a goal concerns all coefficients, apply the coefficient map and simplify. If the goal concerns algebraic equality, try `ext n` to reduce it to coefficient equality; this is the polynomial version of function extensionality.

Avoid defining polynomial expressions by hand as coefficient functions unless the coefficient function itself is the subject of the theorem. The constructors preserve the ring operations and make simplification predictable.

## 2. Degree and the zero polynomial

Degree statements require attention to the zero polynomial. Mathlib provides both an extended-valued `degree` and a natural-valued `natDegree`. The former can represent the degree of zero as negative infinity; the latter uses a natural number and assigns zero polynomial natural degree zero. The natural version is convenient for induction and inequalities, but it does not distinguish zero from a nonzero constant by degree alone.

When a theorem is about the leading term or the true degree, retain a hypothesis `p ≠ 0` if the API requires it. When a theorem is about an upper bound or a recursive computation, `natDegree` is often easier. Do not silently translate between the two conventions: their zero cases have different behavior.

Degree lemmas also encode assumptions about the coefficient structure. For example, the degree of a product behaves additively when the coefficients have no zero divisors; in a ring with zero divisors, leading coefficients can cancel. If a proof of a product-degree formula asks for an integral-domain assumption, that condition is mathematical, not an elaboration inconvenience.

## 3. Evaluation within the coefficient ring

For `p : Polynomial R` and `x : R`, `Polynomial.eval x p` evaluates the polynomial in its own coefficient ring. Evaluation is a ring homomorphism from `R[X]` to `R`, and algebraic identities can usually be proved using `simp`, `ring`, or a theorem about the evaluation map.

```lean
example {R : Type*} [CommRing R] (a : R) :
    (Polynomial.X - Polynomial.C a : Polynomial R).IsRoot a := by
  simp
```

The proof reduces the root condition to evaluation being zero, then simplifies `X` and the constant term at `a`. This is the preferred shape for a routine root calculation: state the mathematical property, unfold only the root predicate if simplification does not already do so, and let the evaluation lemmas normalize the expression.

An evaluation identity can also be proved by expressing the evaluation map as a bundled ring homomorphism. This is helpful when the same evaluation operation is composed with other maps or reused across several lemmas. The homomorphic form exposes preservation of addition and multiplication, while `eval` is convenient for pointwise calculations.

This choice can simplify a multi-stage argument. Suppose a polynomial is first mapped along a coefficient homomorphism and then evaluated in the target ring. Rather than prove a formula separately for zero, one, addition, and multiplication, use the bundled evaluation homomorphism and its composition lemmas. The homomorphism states exactly which operations are preserved, so later proofs can treat evaluation as a structure-preserving map.

## 4. Evaluation in a different ring

Sometimes the coefficients lie in `R`, while the point where the polynomial is evaluated lies in another semiring `S`. For this, `Polynomial.eval₂ f x p` takes a ring homomorphism `f : R →+* S` to transport the coefficients and an element `x : S` for the variable. This is the general-purpose evaluation operation.

The extra map is essential. The expression `p : Polynomial ℚ` can be evaluated at a real or complex number only after its rational coefficients are mapped into the target. In concrete algebra, the required map may be an `algebraMap`; in a theorem about arbitrary coefficient transport, it should remain an explicit ring homomorphism.

The distinction can be summarized as follows:

```text
Polynomial R --eval at x in R------------------> R
     │
     └------ map coefficients by f, eval at x --> S
```

Use `eval₂` when the coefficient map is part of the data. It is particularly useful for compatibility statements: mapping coefficients and evaluating in the target can be compared through a single theorem rather than by expanding the polynomial sum.

## 5. Algebra evaluation and universal properties

If `A` is an `R`-algebra, `Polynomial.aeval x p` evaluates `p : Polynomial R` at `x : A` using the algebra structure. This differs from `eval₂` in the interface: the coefficient map is inferred from the `Algebra R A` instance instead of being passed explicitly.

For example, the complex number `Complex.I` is a root of the real polynomial `X^2 + 1`:

```lean
example :
    Polynomial.aeval Complex.I
      (Polynomial.X ^ 2 + 1 : Polynomial ℝ) = 0 := by
  simp
```

This is an instance of a universal property. A polynomial ring is freely generated by its coefficients and one variable. To define a ring homomorphism out of `R[X]`, it is enough to specify a compatible map on coefficients and the image of `X`. Evaluation packages that construction. Prefer `aeval` when the algebra structure is central to the theorem; prefer `eval₂` when the coefficient map must remain visible or is not the canonical algebra map.

This choice often determines the shape of later lemmas. If a theorem quantifies over every `R`-algebra, write it using `aeval`; if it compares a polynomial after applying a particular `RingHom`, use `eval₂` or `map` explicitly.

## 6. Roots as predicates and as multisets

The predicate `p.IsRoot a` means that evaluation at `a` gives zero. It is a proposition about one element. The theorem `Polynomial.IsRoot.def` connects it to evaluation. This predicate is appropriate for statements such as “every solution of this equation is a root” or “a fixed element is a root of a product.”

The object `p.roots`, by contrast, is a multiset of roots with multiplicity. It is defined under domain assumptions, and its behavior on the zero polynomial is chosen for a useful API rather than as a literal enumeration of all elements satisfying the predicate. Therefore, keep these questions distinct:

- Is a particular element a root? Use `IsRoot` and evaluation.
- Is the set of roots finite? Use a finiteness theorem with a nonzero polynomial hypothesis.
- How many roots occur, counting multiplicity? Use `roots` and degree bounds.

For a nonzero polynomial over an integral domain, Mathlib proves that a finite subset of its roots has cardinality at most its natural degree. The assumptions matter: over a ring with zero divisors, nonzero polynomials can have unexpectedly many roots, and the zero polynomial vanishes everywhere. When a root-counting theorem has both `[IsDomain R]` and `p ≠ 0`, each rules out one of these failures.

## 7. Divisibility and linear factors

The factor theorem connects a root `a` of `p` to divisibility by the linear factor `X - C a`. In formal proofs, the key is to use the library theorem in the direction needed rather than manually performing polynomial division.

There are two common proof goals:

1. From a root hypothesis, produce a factorization `p = (X - C a) * q` for some polynomial `q`.
2. From divisibility by `X - C a`, conclude that `a` is a root.

The second direction often follows by evaluating both sides at `a`, after simplification makes the factor vanish. The first direction uses the factor theorem and may require a coefficient-ring assumption. Search for the theorem by the mathematical names `IsRoot`, `dvd`, `X_sub_C`, and `eval` rather than unfolding polynomial division.

As a small example of keeping the interfaces separate, a root of one factor is automatically a root of a product:

```lean
example {R : Type*} [CommRing R] (p q : Polynomial R) (a : R)
    (hp : p.IsRoot a) : (p * q).IsRoot a := by
  rw [Polynomial.IsRoot.def] at hp ⊢
  simp [hp]
```

The proof first converts the proposition into an equation about evaluation. The evaluation map turns the product into a product, and the hypothesis makes one factor zero. This pattern is more stable than unfolding the coefficient sum for `p * q`.

Factorization arguments also benefit from separating algebraic normalization from root reasoning. A `ring` proof can establish a polynomial identity; an `IsRoot` theorem can then translate that identity into a claim about evaluations. This avoids asking one tactic to solve a goal that mixes coefficient algebra and logical root properties.

## 8. Mapping coefficients and changing the target

For a ring homomorphism `f : R →+* S`, `Polynomial.map f p` transports every coefficient. The coefficient theorem for `map` is a useful interface when a proof must compare a specific coefficient on both sides. Evaluation compatibility then describes how `map` interacts with `eval₂`.

When roots are considered in an extension ring, be precise about the direction of coefficient transport. A polynomial over `R` can be evaluated at a point in an `R`-algebra using `aeval`; a polynomial over `S` can be mapped along a homomorphism from `S` to another coefficient ring. These constructions have different types and different mathematical meanings.

For injective coefficient maps, roots in the target can sometimes be related back to roots in the source. The injectivity hypothesis prevents distinct coefficients from collapsing during transport. The root API has dedicated theorems for these situations; applying an arbitrary coefficient map without injectivity does not preserve all polynomial information. For example, a nonzero polynomial may map to zero if every coefficient maps to zero, so a root statement after mapping may become vacuous.

The most common type error here is to attempt `eval x p` when `x` belongs to the extension and not the coefficient ring. Change to `aeval x p` when an algebra instance is available, or use `eval₂ f x p` with an explicit coefficient map. Do not coerce the polynomial's coefficients manually.

## 9. A proof workflow

1. Decide whether the goal concerns polynomial equality, evaluation, a root predicate, or a root multiset.
2. Keep the polynomial as an abstract element of `Polynomial R`; use constructors such as `C`, `X`, and `monomial`.
3. Choose `eval`, `eval₂`, or `aeval` by inspecting where the coefficients and evaluation point live.
4. Use `simp` for constructor and evaluation equations, then `ring` for residual polynomial identities.
5. For degree or root-counting results, state nonzero and domain assumptions before applying the theorem.
6. Use the factor theorem to move between roots and linear divisibility; do not reimplement division unless the quotient is needed explicitly.

This sequence keeps type-level choices separate from algebraic calculation. Most failures occur because the chosen evaluation operation has the wrong source or target, or because the zero polynomial has not been handled.

For a theorem combining a root bound and a factorization, use a two-stage proof. First establish each proposed root with an evaluation calculation or a factor theorem. Then form the finite set of distinct roots and apply the cardinality bound. If multiplicity matters, use the multiset API and degree identity rather than counting distinct elements. This distinction prevents a common mathematical mismatch: the degree bounds total multiplicity, while a set cardinality counts each root only once.

## 10. Common failure modes

### Evaluation uses the wrong target ring

`eval` expects a point in the coefficient ring. Use `aeval` or `eval₂` for an extension.

### The zero polynomial breaks a degree or root theorem

Check whether the result uses `degree` or `natDegree`, and whether it requires a nonzero hypothesis.

### A polynomial equality is expanded into coefficients too early

Try algebraic normalization first. Use `ext n` only when the coefficient comparison is the natural proof.

### Root counting lacks a domain assumption

Check the algebraic setting. The finite-root theorem depends on a no-zero-divisors hypothesis.

### `simp` does not expose the root condition

Rewrite with `Polynomial.IsRoot.def`, then simplify evaluation. Keep the unfolding local to that step.

## 11. Exercises

1. Prove that a constant polynomial evaluates to its coefficient at any point in the same semiring.
2. Show that `a` is a root of `X - C a` using the evaluation interface.
3. Prove that a root of `p` is a root of `p * q`. Identify the ring assumptions needed by the evaluation proof.
4. State a theorem using `eval₂` for a polynomial whose coefficient map is an arbitrary ring homomorphism.
5. Rewrite the complex-root example using an explicit coefficient map and `eval₂`.
6. Find the Mathlib theorem bounding the cardinality of a finite subset of the roots of a nonzero polynomial. Explain each typeclass assumption.
7. Use a factor theorem to convert a root hypothesis into divisibility by a linear factor.
8. Explain why a root predicate and a root multiset answer different questions about the zero polynomial.

## Summary

Use the polynomial constructors and coefficient interface instead of exposing the finite-support representation. Choose `eval` for evaluation in the coefficient ring, `eval₂` for an explicit coefficient map into another semiring, and `aeval` for evaluation in an algebra. Use `IsRoot` for a proposition about an element and `roots` for a multiset with multiplicities. Degree and root-counting arguments must handle the zero polynomial and preserve domain assumptions. The factor theorem provides the bridge between roots and linear divisibility.

## Further reading

- [Mathlib: Polynomial evaluation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Eval/Defs.html)
- [Mathlib: Polynomial roots and degree bounds](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Roots.html)
- [Mathematics in Lean: Polynomials](https://leanprover-community.github.io/mathematics_in_lean/C09_Groups_and_Rings.html)
