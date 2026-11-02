# Chapter 47 — Ergodic Averages and Empirical Measures

> **Audience.** This chapter assumes familiarity with measure-preserving maps, ergodicity, finite sums, and convergence in norm. It develops orbit averages, empirical measures, existence of invariant probability measures, and the Hilbert-space mean ergodic theorem.

Long-run questions usually concern averages rather than individual states. Given a transformation `f` and an observable `g`, the average of `g` along the first `n` iterates is

\[
  \frac1n\sum_{k=0}^{n-1} g(f^k(x)).
\]

This expression connects finite computation with invariant measure: the values observed along one orbit can be packaged as an empirical measure, and cluster points of those measures can be invariant. A second route views composition by `f` as an operator and studies its averages in a normed or Hilbert space.

Mathlib provides the algebraic `birkhoffSum` and `birkhoffAverage` definitions, an empirical-measure construction, a Krylov–Bogolyubov existence theorem, and the von Neumann mean ergodic theorem for contractions on Hilbert spaces. These interfaces are related, but they prove different kinds of convergence. A robust formalization names the averaging object first and selects a theorem only after identifying the topology and limit being claimed.

## Learning objectives

By the end of the chapter, you should be able to:

- define finite orbit sums and normalized Birkhoff averages;
- use the additive and composition laws of averages;
- relate empirical measures to orbit averages of observables;
- use compactness to obtain an invariant probability measure;
- distinguish mean convergence in a Hilbert space from pointwise ergodic convergence;
- identify the zero-length convention and other boundary cases in an average.

## 1. Orbit sums and Birkhoff averages

Let `f : α → α` be a self-map and let `g : α → M` be an observable with values in an additive module. The Birkhoff sum of length `n` is

\[
  S_n g(x)=\sum_{k\in\operatorname{range}(n)}g(f^k(x)),
\]

and when the scalar type supports division, the normalized average is

\[
  A_n g(x)=\frac{1}{n}S_n g(x).
\]

Mathlib calls these `birkhoffSum` and `birkhoffAverage`. The orbit iterate is the `k`th function iterate of `f`; it is not a separately defined stochastic trajectory. For a deterministic dynamical system, this is the entire trajectory from `x`.

The sum is algebraic. Its basic laws—additivity in `g`, behavior under a homomorphism, and relationships between averaging `g ∘ f` and shifting the starting point—can be established before any measure is introduced. This is an important design separation: finite orbit identities do not require measure preservation or ergodicity.

The normalized average needs more structure. The library definition uses an auxiliary division semiring `R` to interpret division by the natural-number length as scalar multiplication by `(n : R)⁻¹`. Its result type `M` is an additive commutative monoid with an `R`-module structure. Although `R` appears in the definition, Mathlib proves that the value is independent of the chosen compatible division semiring. That independence is a reminder to expose only the minimal algebra required by the theorem.

At length zero the sum is zero and the average is defined as zero. This is a convenient total definition, not the mathematical average of an empty list. Any theorem whose informal statement divides by `n` should either assume `n > 0` or explicitly account for the zero case.

## 2. The algebraic API for averages

The average is linear in the observable whenever the target supports the relevant additive and scalar operations:

\[
  A_n(g+h)(x)=A_n g(x)+A_n h(x),
  \qquad
  A_n(-g)(x)=-A_n g(x).
\]

An additive homomorphism on the codomain commutes with a finite average. This lets a proof move from vector-valued observables to coordinates, or map a result through a linear functional without reopening the finite sum.

There is also a shift identity. Averaging the observable `g ∘ f` starting at `x` is the same as averaging `g` starting at `f x`. The two finite lists differ only by the initial or terminal term depending on which unnormalized identity is used. For normalized averages, the exact statement supplied by the API is preferable to an informal “shift the sum” argument, since the endpoint term and the length matter.

If `g ∘ f = g`, then every positive-length average of `g` is just `g`. Each summand is identical, so the result is immediate after handling scalar division. Likewise, if `x` is a fixed point of `f`, then every average of any `g` along the orbit of `x` is `g x`. These are strong regression examples for an averaging API: one checks invariance of the observable separately from fixedness of the state.

In Lean, first rewrite the goal to one of the named average identities. Then handle only the remaining algebra. Expanding `birkhoffAverage` into an inverse scalar times a sum too early can create unnecessary goals about `Finset.range`, function iteration, and division by zero.

## 3. Worked example: averages on a finite cycle

Let `α = Fin n` with `n > 0`, and let `f` rotate every state forward by one position. For any observable `g : Fin n → ℝ`, the orbit from any starting point visits every state exactly once per period. Therefore

\[
  A_n g(x)=\frac1n\sum_{y\in\mathrm{Fin}\ n}g(y).
\]

The value is independent of `x`. Under the uniform probability measure, the right side is also the space integral of `g`. This is a finite instance where a long-run orbit average exactly matches a spatial average after one period.

The proof has three independent components. First, show that the first `n` iterates of `x` are a permutation of the finite state type. Second, rewrite the sum over orbit positions as a sum over all states. Third, identify the uniform expectation with the normalized finite sum. The ergodicity of the cyclic rotation is not needed for the finite-period identity itself, though it explains why this orbit covers the entire space.

If the transformation instead rotates by `k` positions with `gcd(k,n)=d`, each orbit has length `n/d` and there are `d` orbits. The time average from `x` is then the average over its orbit, not necessarily the global uniform average. When `d>1`, choose an observable that distinguishes two orbits to see the difference. This is a useful counterexample to any proof that appears to derive a space average from invariance alone.

For the formal proof, use `Finset.sum_bij` or an equivalent finite reindexing lemma to express the orbit permutation. Avoid expanding every iterate by `simp` if the proof can first establish that the orbit map is a bijection. The bijection is the mathematical reason the reindexing is valid and is reusable for every observable.

## 4. From invariant observables to constant averages

If an observable is exactly invariant under the transformation, its finite average is unchanged at every length. Chapter 46 gave the measure-theoretic counterpart: under ergodicity, an almost-everywhere invariant measurable function is almost everywhere constant. The two statements operate at different levels:

- exact invariance gives an identity of finite averages at each point;
- ergodicity plus almost-everywhere invariance gives essential constancy;
- an ergodic theorem, when available, can identify the limiting time average with a space average.

Do not collapse these into one theorem. In particular, the identity `g ∘ f = g` is much stronger than saying that the averages `A_n g` converge. Conversely, convergence of averages need not make the original observable invariant.

For a measure-preserving ergodic system and an integrable observable, the classical pointwise ergodic theorem says that time averages converge almost everywhere to the integral of the observable. It is a deep theorem with measurable and integrability hypotheses. Mathlib's algebraic Birkhoff-average API does not make that conclusion automatic. The chapters here use only the theorem interfaces that are documented: finite averaging identities, empirical measures, and the Hilbert-space mean theorem described below.

This boundary is a useful library-search lesson. A definition named “Birkhoff average” does not imply that every theorem called “Birkhoff ergodic theorem” is present for all function spaces and modes of convergence. Read the result type: `Tendsto` in a norm topology, almost-everywhere convergence of scalar functions, and convergence of probability measures are different conclusions.

## 5. Empirical measures record orbit statistics

An empirical measure assigns equal weight to the points visited in a finite orbit segment. Informally,

\[
  \mathsf{Emp}_{n,x}
  =\frac{1}{n+1}\sum_{k=0}^{n}\delta_{f^k(x)}.
\]

Mathlib's `MeasureTheory.empiricalMeasure f x n` uses `n+1` iterates, so it is defined for every natural `n` and is a probability measure even at `n=0`. The extra `+1` avoids normalizing by zero and should be kept in mind when comparing theorem statements with the convention that calls the first `n` observations an empirical law.

The central bridge theorem identifies integration against an empirical measure with the corresponding orbit average of an observable. In schematic form,

\[
  \int g\,d\mathsf{Emp}_{n,x}
  =A_{n+1}g(x).
\]

This theorem turns weak convergence of measures into convergence of averages of continuous bounded test functions. It also lets a proof move in the other direction: if empirical measures converge and the test function is continuous and bounded, then the associated orbit averages converge to the integral against the limiting measure.

The empirical measure is a reusable packaging of data. Instead of carrying a finite sum for every observable, construct one measure and apply the integral identity. This makes the proof shorter when many observables are involved and exposes compactness or weak-convergence arguments that are invisible in raw sums.

## 6. Worked example: empirical measures on a periodic orbit

Return to the finite cycle from Section 3. Once `n` covers exactly one full period, the empirical measure is the uniform law on the cycle. Integrating `g` against it gives the orbit average. If the cycle covers the whole state space, this is the uniform spatial expectation; if the transformation has several cycles, it is the uniform measure on the particular cycle containing `x`.

This example can be formalized without a general weak-convergence theorem. Represent each Dirac measure by its atom, form the finite sum, and prove the integration identity by the finite sum formula for integration. Then use a permutation of the state type to identify the full-cycle case. The theorem `integral_empiricalMeasure_eq_birkhoffaverage` packages the first part for a general measurable type under its stated assumptions.

The period-length convention is easy to get wrong. For a cycle of size `m`, the empirical measure with parameter `m-1` contains `m` points, because it uses `n+1`. Writing this substitution as a small helper lemma prevents off-by-one errors from spreading through the subsequent invariance proof.

For an orbit segment that is not a full period, the empirical measure is generally not invariant. Shifting the segment drops its first atom and adds a new terminal atom; the difference is a boundary term whose normalized mass becomes small as the segment grows. That observation is the finite-sum core of the invariant-cluster-point argument.

## 7. Existence of invariant measures by compactness

The Krylov–Bogolyubov strategy starts with empirical measures. On a compact topological space, probability measures have enough compactness properties that a sequence of empirical measures admits a cluster point. The boundary-term identity shows that applying the transformation to an empirical measure changes it only by a vanishing endpoint contribution. Any cluster point is therefore invariant.

Mathlib provides `MeasureTheory.exists_measurePreserving_probabilityMeasure` for a continuous map on a compact Hausdorff space, together with a version for a compact forward-invariant subset of a possibly larger ambient space. The theorem packages the topological compactness and weak-convergence argument. A user of the theorem still needs to supply the continuity and compactness assumptions in the exact form required by the current API.

The proof pattern is a general one in formal mathematics:

```text
finite orbit segment
        │
        ▼
empirical probability measure
        │ compactness
        ▼
cluster point ── boundary term vanishes ──▶ invariant measure
```

Notice what the theorem gives and what it does not. It gives existence of at least one invariant probability measure. It does not imply uniqueness, ergodicity, or convergence of the entire empirical-measure sequence. Those require additional structural hypotheses. On a compact system with several invariant components, different initial points or subsequences can lead to different invariant limits.

When a proof only needs existence, invoke the theorem rather than reproducing weak compactness and Riesz representation. If a later result needs support on a particular compact invariant set, use the forward-invariant variant and keep the ambient space and supporting subset explicit.

## 8. The mean ergodic theorem in a Hilbert space

There is a different averaging problem for a linear operator `T` on a Hilbert space `H`. For a vector `v`, form

\[
  M_n(v)=\frac1n\sum_{k=0}^{n-1}T^k v.
\]

If `T` is a contraction, the von Neumann mean ergodic theorem says that these averages converge in norm to the orthogonal projection of `v` onto the subspace of fixed vectors. The limiting vector is the component of `v` that survives the action of `T` unchanged.

Mathlib states this using `birkhoffAverage` applied to the linear map and the identity observable. The Hilbert-space theorem requires completeness and an operator norm bound `‖T‖ ≤ 1`. The library also exposes a normed-space formulation that isolates a projection and a dense-range condition. This separation is useful: the algebraic proof about `T - 1` can be reused independently of inner-product geometry.

This is convergence in norm of vectors. It is not pointwise convergence of functions on a probability space, and it is not weak convergence of empirical measures. The word “mean” here refers to Cesàro averages in a Hilbert space. To use it for a Koopman operator induced by a measure-preserving map, construct the appropriate function space, verify that composition defines a contraction or isometry, and identify fixed functions. The theorem does not remove those setup obligations.

## 9. Compare the three convergence interfaces

Three related limits now appear in the chapter:

| Object being averaged | Typical conclusion | Main proof interface |
| --- | --- | --- |
| Observable values along an orbit | scalar or vector average converges | pointwise or norm `Tendsto` theorem |
| Dirac measures along an orbit | empirical measures converge weakly | probability-measure topology and test functions |
| Iterates of a linear operator | Cesàro averages converge in norm | mean ergodic theorem and fixed subspace |

These limits can imply each other under additional assumptions, but the conversion is never automatic. Weak convergence tests continuous bounded functions; norm convergence controls a vector norm; almost-everywhere convergence permits a null exceptional set. The target filter and topology are part of the theorem statement, not formatting details.

In Lean, inspect the codomain of `Tendsto` before searching for simplification lemmas. A limit in `ProbabilityMeasure X`, a limit in `H`, and an almost-everywhere limit of functions have different neighborhoods and different proof principles. State intermediate lemmas using the type that best matches the desired conclusion, then use a documented bridge theorem only when its hypotheses fit.

## 10. A proof workflow

1. Define the transformation and observable, then choose sum or average according to the theorem's boundary convention.
2. Prove finite orbit identities before introducing a measure.
3. For a length-normalized result, state and use `n > 0` when needed.
4. Use linearity and composition lemmas to manipulate averages without unfolding finite sums.
5. Construct an empirical measure when the proof needs to reason about many observables or weak limits.
6. Use the empirical integration theorem to move between orbit averages and expectations.
7. Use compactness-based existence only after checking continuity and compactness assumptions.
8. For Hilbert averages, establish completeness, linearity, and the contraction bound before invoking the mean theorem.
9. Name the mode of convergence explicitly: pointwise, almost everywhere, in norm, or weakly as measures.

## 11. Common failure modes

### Dividing by zero is overlooked

The library totalizes averages at length zero. State positivity if the mathematical expression uses `1/n`.

### The empirical-measure index is off by one

`empiricalMeasure f x n` uses `n+1` iterates. Translate conventions in a helper lemma.

### Invariance is inferred from one finite segment

An empirical measure is generally only approximately invariant. Exact invariance is obtained for a limit point, not for each finite segment.

### Existence is confused with uniqueness

Compactness gives an invariant probability measure, not a unique one.

### Mean convergence is confused with pointwise convergence

The Hilbert mean theorem gives norm convergence of operator averages. A pointwise ergodic theorem is a different result with different hypotheses.

### An algebraic average is mistaken for a probabilistic theorem

`birkhoffAverage` defines a finite sum. It does not itself assert any asymptotic convergence.

## 12. Exercises

1. Define the Birkhoff sum and average in mathematical notation.
2. Explain why the average has a total value at `n=0` and why this convention differs from an average over a nonempty list.
3. Prove that an invariant observable has the same average at every positive length.
4. Compute the average of an observable over a full cycle on `Fin n`.
5. Describe what changes when rotation by `k` has more than one orbit.
6. State the relationship between integration against an empirical measure and a Birkhoff average.
7. Why does Mathlib's empirical measure use `n+1` iterates?
8. Outline the boundary-term argument that makes cluster points of empirical measures invariant.
9. State what the Krylov–Bogolyubov theorem supplies and list two conclusions it does not supply.
10. Describe the limit in the Hilbert-space mean ergodic theorem.
11. Distinguish weak convergence of measures, norm convergence, and almost-everywhere convergence.
12. Locate `birkhoffAverage_congr_ring`, `integral_empiricalMeasure_eq_birkhoffaverage`, and `exists_measurePreserving_probabilityMeasure` in the current documentation.

## Summary

Birkhoff sums and averages encode finite orbit statistics. Empirical measures package those statistics as probability measures, and integration against them recovers orbit averages. Compactness can turn empirical measures into invariant measures, while the Hilbert-space mean ergodic theorem gives norm convergence of operator averages to a projection onto fixed vectors. Each construction has distinct assumptions and a distinct notion of limit; finite averages alone do not assert asymptotic convergence.

## Further reading

- [Mathlib: Birkhoff sums and averages](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Dynamics/BirkhoffSum/Average.html)
- [Mathlib: Empirical measures and the Krylov–Bogolyubov theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Dynamics/Ergodic/EmpiricalMeasure.html)
- [Mathlib: Von Neumann mean ergodic theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/MeanErgodic.html)
- Chapters 45–46 for invariant kernels, measure-preserving maps, and ergodicity.
