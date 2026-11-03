# Chapter 48 — Total Variation and Markov Chain Convergence

> **Audience.** This chapter assumes familiarity with finite Markov kernels, invariant measures, finite sums, and inequalities. It develops total variation distance, coupling, contraction, and geometric mixing bounds, with an emphasis on finite-state formalization.

An invariant probability describes where a Markov chain can settle, but it does not say how quickly the chain approaches that distribution. Quantitative convergence requires a distance between probability measures and an estimate for how each transition changes that distance. Total variation is particularly useful because it directly controls differences in event probabilities and admits coupling and contraction arguments.

Mathlib defines total variation distance for finite measures and proves its basic metric properties. Its convention for probability measures is twice the most common probability-theory convention. The Markov-chain contraction arguments in this chapter are developed at the finite-state level so the role of the kernel row sums remains visible. A proof should check normalization carefully and should not assume that every probabilistic coupling theorem already has a general kernel-level wrapper in the library.

## Learning objectives

By the end of the chapter, you should be able to:

- state Mathlib's total variation convention and relate it to the usual probability distance;
- express total variation on a finite state space as a sum of pointwise differences;
- prove that a Markov transition contracts total variation;
- turn a coupling with high meeting probability into a distance bound;
- derive geometric mixing from a minorization condition;
- separate an invariant distribution from a quantitative convergence estimate.

## 1. Total variation measures discrepancy

For finite measures `μ` and `ν`, total variation distance measures the total mass of their signed difference. Mathlib provides an extended nonnegative version `etvDist` and a real-valued version `tvDist`. If either measure is not finite, their conventions differ: `etvDist` is infinite, while `tvDist` is defined as zero. In probability arguments the measures are finite, but it is still important to retain the finiteness hypotheses when using theorems that identify zero distance with equality.

For probability measures, `tvDist` takes values in `[0,2]`. Many probability texts define distance as

\[
  d_{\mathrm{TV}}(\mu,\nu)
  =\sup_{A}|\mu(A)-\nu(A)|,
\]

which takes values in `[0,1]`. Under the standard convention,

\[
  \mathsf{tvDist}(\mu,\nu)=2d_{\mathrm{TV}}(\mu,\nu).
\]

On finite discrete spaces, Mathlib's distance is the `ℓ¹` difference of the point masses:

\[
  \mathsf{tvDist}(\mu,\nu)
  =\sum_{x}|\mu\{x\}-\nu\{x\}|.
\]

The standard probability distance is half this sum. This factor of two propagates into coupling inequalities and mixing-time definitions, so choose one convention at the beginning of a development and convert only at the boundary.

The measure-theoretic definition is not restricted to discrete spaces. Mathlib characterizes `tvDist` through a supremum over finite measurable partitions. On a finite type, those partitions reduce to a finite combinatorial object and the formula simplifies to the sum over atoms.

## 2. Worked example: two point masses

Let `μ` assign all probability to state `a`, and `ν` assign all probability to a distinct state `b`. Their point-mass vectors differ by `1` at `a` and by `1` at `b`, so

\[
  \mathsf{tvDist}(\mu,\nu)=|1-0|+|0-1|=2.
\]

Under the usual probability convention, `dTV(μ,ν)=1`. The event `{a}` separates the two laws completely: it has probability one under `μ` and zero under `ν`.

For two probability measures on a finite state type, a useful proof plan is: express each measure by its atom weights; prove the finite-sum formula for `tvDist`; then reduce all inequalities to real arithmetic over the coordinates. Do not mistake the set supremum formula for the unnormalized `ℓ¹` formula—the latter contains the factor of two relative to the maximum event discrepancy.

This example is a small but effective normalization check. If a proposed theorem says that a coupling mismatch probability is at least `tvDist` without a factor of two, it is likely using the standard half-normalized distance. If it uses Mathlib's `tvDist`, the corresponding upper bound has a factor of two.

## 3. Applying a kernel cannot increase distance

Let `K` be a Markov kernel on a finite state space. For probability vectors `μ` and `ν`, the distributions after one transition are

\[
  (\mu K)(y)=\sum_x\mu(x)K(x,y),
  \qquad
  (\nu K)(y)=\sum_x\nu(x)K(x,y).
\]

Then

\[
\begin{aligned}
  \mathsf{tvDist}(\mu K,\nu K)
  &=\sum_y\left|\sum_x(\mu(x)-\nu(x))K(x,y)\right|\\
  &\leq\sum_y\sum_x|\mu(x)-\nu(x)|K(x,y)\\
  &=\sum_x|\mu(x)-\nu(x)|\sum_yK(x,y)\\
  &=\mathsf{tvDist}(\mu,\nu).
\end{aligned}
\]

The key step is the triangle inequality; the last step uses that each transition row has total mass one. If a kernel is sub-Markov, the row sums can be less than one and the conclusion requires a different statement or additional hypotheses.

This is the data-processing principle for a Markov transition: applying the same randomization to two initial laws cannot make them easier to distinguish. In formalization, prove a finite-sum inequality for the signed coordinate differences and invoke the row-sum-one lemma. This is more stable than unfolding the definition of `tvDist` and asking a nonlinear arithmetic tactic to discover the triangle-inequality argument.

Mathlib's total variation API supplies the distance and its general measure-theoretic properties. Depending on the kernel interface and desired generality, the contraction theorem may need to be proved as a local finite-state lemma by lifting measures through the kernel. State the specialization in a helper theorem so later chain arguments do not repeat the sum manipulation.

## 4. Invariance plus contraction gives convergence

Suppose `π` is invariant under `K`, so `πK=π`. Apply the one-step contraction repeatedly:

\[
  \mathsf{tvDist}(\mu K^n,\pi)
  =\mathsf{tvDist}(\mu K^n,\pi K^n)
  \leq\mathsf{tvDist}(\mu,\pi).
\]

This proves nonexpansion, but not convergence to zero. A distance can remain constant under a transition. The deterministic three-cycle from Chapter 45 preserves the uniform distribution and is irreducible, yet a point mass keeps rotating and its total variation distance from uniform remains constant.

To get a rate, prove a strict contraction. If for some `ρ<1`,

\[
  \mathsf{tvDist}(\mu K,\nu K)
  \leq ρ\,\mathsf{tvDist}(\mu,\nu)
\]

for every pair of probability measures, induction yields

\[
  \mathsf{tvDist}(\mu K^n,\pi)
  \leq ρ^n\mathsf{tvDist}(\mu,\pi)
  \leq 2ρ^n.
\]

The final constant uses the `[0,2]` range for Mathlib's convention. If a mixing-time definition uses the half-normalized distance, the bound is `ρ^n`. This estimate also proves uniqueness of an invariant probability: if `π₁` and `π₂` are both invariant, then their distance is at most `ρ` times itself, forcing it to be zero.

## 5. Minorization yields a strict contraction

A useful sufficient condition for strict contraction is a common component in every transition row. Suppose there is a probability measure `λ` and a constant `ε` with `0<ε≤1` such that

\[
  K(x,A)\geq ε\lambda(A)
\]

for every state `x` and measurable set `A`. If `ε<1`, each row can be decomposed as

\[
  K(x,\cdot)=ε\lambda+(1-ε)R(x,\cdot),
\]

where `R` is again a Markov kernel. For an initial law `μ`,

\[
  \mu K=ε\lambda+(1-ε)\mu R.
\]

The same common term appears for `ν`, so it cancels when the two output measures are subtracted. Applying nonexpansion to `R` gives

\[
  \mathsf{tvDist}(\mu K,\nu K)
  \leq (1-ε)\mathsf{tvDist}(\mu,\nu).
\]

If the minorization only holds for `K^m`, then the same argument contracts every `m` steps. This block version covers periodic-looking one-step behavior that becomes uniformly mixing after a bounded number of transitions.

The formal proof has a useful architecture: construct the residual row measure, prove it is nonnegative and has mass one, derive the affine decomposition, then cancel the common measure and apply the TV bound to the residual kernel. Keep `ε=1` separate, since the residual denominator vanishes and all rows are already equal to `λ`.

## 6. Worked example: a reset chain

Let `λ` be any probability measure on a finite state space and define

\[
  K(x,\cdot)=ε\lambda+(1-ε)\delta_x,
  \qquad 0<ε≤1.
\]

At each step, the chain resets to an independent draw from `λ` with probability `ε`; otherwise it stays where it is. The law `λ` is invariant, since

\[
  \lambda K=ε\lambda+(1-ε)\lambda=\lambda.
\]

For two initial laws, the reset part is identical and the remaining part has weight `1-ε`. Therefore

\[
  \mathsf{tvDist}(\mu K,\nu K)
  \leq(1-ε)\mathsf{tvDist}(\mu,\nu).
\]

Starting from any `μ`, the distance to stationarity is at most `2(1-ε)^n` in Mathlib's convention. Under the standard probability convention it is at most `(1-ε)^n`.

This example is well suited to a finite Lean formalization. Define the row as a convex combination of `λ` and the Dirac probability. Prove the row has total mass one and that `λ` is invariant. Then establish the contraction either by minorization or by direct simplification of the mixture. The direct proof is short; the minorization proof exercises a reusable theorem that applies to more complicated kernels.

The `ε=1` case is instructive: one transition forgets the initial state completely, and the output is exactly `λ`. The general geometric estimate includes this case as an immediate zero-distance conclusion, but the residual-kernel proof should branch before dividing by `1-ε`.

## 7. Coupling turns shared randomness into a bound

A coupling of probability measures `μ` and `ν` is a joint probability distribution on pairs `(X,Y)` whose marginals are `μ` and `ν`. For every event `A`, the indicators of `X∈A` and `Y∈A` agree whenever `X=Y`. Hence

\[
  |\mu(A)-\nu(A)|\leq\mathbb{P}(X\ne Y).
\]

Taking the supremum over events gives the standard probability-distance inequality

\[
  d_{\mathrm{TV}}(\mu,\nu)\leq\mathbb{P}(X\ne Y),
\]

or, in Mathlib's normalization,

\[
  \mathsf{tvDist}(\mu,\nu)\leq2\,\mathbb{P}(X\ne Y).
\]

To compare two Markov chains, construct a joint transition that has the desired kernel as each marginal. Once the two coordinates meet, use identical randomness at later steps so they remain together. If `τ` is the meeting time, then

\[
  \mathsf{tvDist}(\mathcal{L}(X_n),\mathcal{L}(Y_n))
  \leq2\,\mathbb{P}(\tau>n).
\]

Thus a tail bound for the meeting time becomes a convergence bound for the marginals. Coupling proofs are often more intuitive than summing all transition paths, but formalizing them requires a joint kernel and proofs that both marginals are preserved. On finite types, define the joint transition explicitly and verify its marginals by finite sums.

The coupling inequality applies to any coupling, not only a maximal one. A maximal coupling attains the smallest possible mismatch probability, which equals the standard TV distance, but constructing such a coupling is an additional theorem. For a convergence proof, a convenient coupling with a tractable meeting probability is often enough.

## 8. Worked example: a common reset coupling

For the reset chain in Section 6, run two copies using the same Bernoulli reset decision and the same reset sample. If a reset occurs, both chains jump to the same state. After that, use shared randomness to keep them equal. The probability that the chains have not yet coupled after `n` steps is at most `(1-ε)^n`.

The coupling bound therefore gives standard TV distance at most `(1-ε)^n`, or Mathlib `tvDist` at most `2(1-ε)^n`. This agrees with the contraction argument. The two proofs package the same common randomness differently: minorization isolates a common part of each row, while coupling makes that common part an explicit event in a joint process.

In code, separate three definitions: the one-chain kernel, the joint coupling kernel, and the projections from the product state space. Prove that each projection of the joint transition has the original transition as its marginal. Then prove the diagonal is absorbing under the coupled dynamics. The final TV estimate can be derived from the mismatch probability without unfolding the original chain's `n`-step distribution.

## 9. From a contraction rate to mixing time

For a finite irreducible chain with stationary law `π`, a common worst-case mixing-time convention is

\[
  t_{\mathrm{mix}}(\delta)
  =\min\left\{n:\sup_x d_{\mathrm{TV}}(K^n(x,\cdot),\pi)\leq\delta\right\}.
\]

Under an `m`-step contraction factor `ρ<1`, the bound `dTV≤ρ^⌊n/m⌋` implies

\[
  t_{\mathrm{mix}}(\delta)
  \leq m\left\lceil\frac{\log(1/\delta)}{\log(1/ρ)}\right\rceil,
\]

with the usual care about signs and rounding because `0<ρ<1`. In a formal proof, it is usually clearer to establish the exponential inequality first and derive a requested natural-number bound afterward. The logarithmic manipulation and ceiling inequalities should be isolated from the probability argument.

Irreducibility and aperiodicity are common hypotheses in finite-chain convergence theorems, but the contraction estimate is a more quantitative sufficient condition. A chain may converge without a uniform one-step minorization; failure of this method does not imply failure of mixing. The point is to prove a usable rate under hypotheses that can be checked in the particular model.

## 10. Finite-state proof architecture

For a transition matrix on `Fin n`, keep the proof in layers:

1. Prove each row is a probability vector.
2. Define the action of the kernel on a probability vector by matrix multiplication.
3. Establish the finite formula for `tvDist`.
4. Prove nonexpansion from the row sums.
5. Add minorization or a coupling construction for strict contraction.
6. Prove the candidate stationary vector is invariant.
7. Combine contraction and invariance to obtain convergence and uniqueness.

This ordering localizes common failures. If the TV formula has the wrong factor, the error appears before any mixing-time argument. If a row is missing mass, nonexpansion fails at the row-sum step. If a minorization residual is not a probability vector, the error appears in its construction rather than buried inside an iterate induction.

### The spectral route for reversible chains

When the kernel is reversible with respect to a full-support stationary law `π`, its transition operator is self-adjoint in the weighted inner product

\[
  \langle f,g\rangle_\pi=\sum_x\pi(x)f(x)g(x).
\]

If constants are the only fixed functions and the operator contracts the orthogonal complement of constants by a factor `ρ<1`, then centered observables decay in `L²(π)` at rate `ρⁿ`. Applying Cauchy–Schwarz converts that bound into a total variation estimate. For a chain started at state `x`, a typical bound has the form

\[
  \mathsf{tvDist}(K^n(x,\cdot),\pi)
  \leq ρ^n\sqrt{\frac{1}{\pi(x)}-1},
\]

under the stated reversibility, full-support, and spectral assumptions. The right side records the initial density's `L²` size, so states with very small stationary mass can give a weaker worst-case bound.

This route is well suited to symmetric or reversible finite chains and connects Chapter 45's detailed balance condition to linear algebra. It is more delicate than minorization: one must identify the weighted inner-product space, establish self-adjointness, isolate the constant eigenspace, and control every other eigenvalue in absolute value. In Lean, keep the matrix representation, weighted inner product, and spectral estimate as separate interfaces. A spectral gap theorem and a coupling theorem may produce different constants, so use the one that matches the structure of the model.

Mathlib's `tvDist` is a general finite-measure distance and has self, symmetry, triangle, and zero-characterization lemmas. For a finite discrete chain, specialize those tools to atom masses and prove the kernel-specific inequalities explicitly. This chapter does not assume a one-call library theorem for every finite Markov-chain coupling or minorization result; such wrappers are good local abstractions to build in a project.

## 11. Common failure modes

### The factor of two is dropped

Mathlib's probability `tvDist` is twice the standard event-supremum distance. Convert conventions explicitly.

### Invariance is treated as convergence

`πK=π` says `π` remains fixed. It does not bound the distance from another starting law.

### A nonexpansion estimate is called mixing

Distance at most its previous value allows equality forever. A strict contraction or another decay argument is needed.

### The Markov row-sum condition is omitted

The finite contraction proof uses `∑_y K(x,y)=1` exactly.

### The coupling is not a coupling

A joint law must have the intended two marginals. Shared randomness alone is not a proof until those marginal identities are verified.

### The residual kernel is used at `ε=1`

The expression dividing by `1-ε` is undefined there. Handle the complete-reset case separately.

### Periodicity is ignored

Irreducibility and stationarity can hold while distributions oscillate. Check the assumptions of the convergence theorem being used.

## 12. Exercises

1. State Mathlib's normalization of `tvDist` for probability measures.
2. Compute `tvDist` between two distinct Dirac probability measures.
3. Derive the finite-state `ℓ¹` formula from point masses.
4. Prove that a finite Markov kernel is nonexpansive in total variation.
5. Show how a strict contraction plus an invariant probability implies uniqueness.
6. Prove the minorization contraction estimate for `0<ε<1`.
7. Handle the `ε=1` case without defining a residual kernel.
8. Construct a coupling for the reset chain and bound its meeting-time tail.
9. Translate a standard coupling inequality into Mathlib's `tvDist` convention.
10. Explain why the deterministic three-cycle does not converge in total variation to its invariant law.
11. Derive a mixing-time bound from an `m`-step geometric contraction.
12. Locate the basic `tvDist` metric and finite-partition characterization in Mathlib's documentation.

## 13. Lean formalization

The first block retains the finite weight-vector calculation from the initial version of this
chapter. The second block states the general metric facts with the hypotheses that Mathlib requires.
The final theorem computes the distance between arbitrary distinct Dirac measures on a space with
measurable singletons. Its proof first exhibits a measurable set separating their supports, then
uses Mathlib's mutually singular formula. This makes the factor-of-two convention executable rather
than leaving it as an informal normalization claim.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def pointMassZero : Weight := fun s => if s = zero then 1 else 0
def pointMassOne : Weight := fun s => if s = one then 1 else 0
def absoluteMassDifference (a b : Nat) : Nat := (a - b) + (b - a)
def totalVariationNumerator : Nat :=
  absoluteMassDifference (pointMassZero zero) (pointMassOne zero) +
  absoluteMassDifference (pointMassZero one) (pointMassOne one)

theorem distinctPointMassesHaveDistanceTwo : totalVariationNumerator = 2 := by decide
```

```lean
theorem exercise_48_1_tvDist_triangle
    {X : Type*} [MeasurableSpace X]
    (μ ν ξ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure ν] :
    MeasureTheory.tvDist μ ξ ≤
      MeasureTheory.tvDist μ ν + MeasureTheory.tvDist ν ξ :=
  MeasureTheory.tvDist_triangle μ ν ξ

theorem exercise_48_12_tvDist_zero_characterization
    {X : Type*} [MeasurableSpace X]
    (μ ν : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν] :
    MeasureTheory.tvDist μ ν = 0 ↔ μ = ν :=
  MeasureTheory.tvDist_eq_zero_iff

theorem tvDist_distinct_dirac_eq_two
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {x y : X} (hxy : x ≠ y) :
    MeasureTheory.tvDist (MeasureTheory.Measure.dirac x)
      (MeasureTheory.Measure.dirac y) = 2 := by
  have hsingular :
      MeasureTheory.Measure.MutuallySingular
        (MeasureTheory.Measure.dirac x) (MeasureTheory.Measure.dirac y) := by
    refine ⟨{y}, MeasurableSet.singleton y, ?_, ?_⟩
    · simp [hxy]
    · simp
  rw [MeasureTheory.tvDist_of_mutuallySingular hsingular]
  norm_num
```

## Summary

Total variation quantifies how distinguishable two laws are. Mathlib's `tvDist` is the unnormalized `ℓ¹` distance for finite probability vectors, so it is twice the common event-supremum convention. Markov kernels are nonexpansive in this metric; minorization yields strict contraction, while couplings convert meeting-time bounds into convergence estimates. Invariance identifies a fixed law, and contraction supplies the quantitative approach to it. These are separate proof obligations that combine only after their constants and hypotheses are explicit.

## Further reading

- [Mathlib: Total variation distance](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/TotalVariation/Defs.html)
- [Mathlib: Total variation identities](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/TotalVariation/Basic.html)
- Chapters 44–45 for irreducibility, invariant measures, and reversibility.
- Chapter 47 for orbit averages and invariant-measure existence.
- Chapters 49–50 for Metropolis–Hastings and Gibbs samplers.
