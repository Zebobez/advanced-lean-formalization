# Chapter 51 — Importance Sampling and Change of Measure

> **Audience.** This chapter assumes familiarity with probability measures, integrals, random variables, and finite probability mass functions. It develops importance sampling through Radon–Nikodym derivatives and finite weighted sums.

Importance sampling estimates an expectation under a target distribution by drawing samples from a different proposal distribution and reweighting each observation. The proof is a change-of-measure identity: the likelihood ratio corrects the proposal law back to the target law. This method connects Mathlib's Radon–Nikodym interface to the finite-sum representation of probability mass functions.

The most important hypotheses concern support and integrability. The proposal must assign positive mass wherever the target does, and the weighted observable must be integrable. When the target is known only up to a normalization constant, one can form a ratio of weighted sums, but that self-normalized estimator is generally biased at a finite sample size. A formal development should keep exact change-of-measure identities separate from statistical approximation statements.

## Learning objectives

By the end of the chapter, you should be able to:

- express a target expectation using a proposal law and a Radon–Nikodym weight;
- state the absolute-continuity and integrability requirements;
- derive finite-state importance weights from point masses;
- distinguish unbiased importance sampling from self-normalized estimation;
- identify support failure and weight degeneracy;
- connect finite PMF sums to Mathlib's integral and change-of-measure APIs.

## 1. The change-of-measure identity

Let `P` be a target probability measure and `Q` a proposal probability measure on the same measurable space. Assume `P` is absolutely continuous with respect to `Q`, written `P ≪ Q`. Its Radon–Nikodym derivative

\[
  L=\frac{dP}{dQ}
\]

is the likelihood ratio. For a nonnegative measurable function `g`,

\[
  \int g\,dP=\int gL\,dQ.
\]

If `g` is real-valued, the corresponding Bochner integral identity requires the relevant integrability conditions. The absolute-continuity hypothesis is what guarantees that a `Q`-almost-everywhere density represents `P`; without it, there may be target mass that no proposal sample can ever observe.

Importance sampling draws `X₁,…,Xₙ` from `Q` and estimates the target expectation by

\[
  \widehat I_n=\frac1n\sum_{i=1}^n L(X_i)g(X_i).
\]

Each summand has expectation `∫g dP`, so the estimator is unbiased whenever the expectation exists. Its variance is controlled by the second moment of `Lg` under `Q`, not merely by the variance of `g` under the target.

If the draws are independent and `Lg` is square-integrable under `Q`, then

\[
  \operatorname{Var}(\widehat I_n)
  =\frac1n\operatorname{Var}_Q(Lg).
\]

This formula makes the proposal-design objective concrete: preserve the exact expectation while reducing the second moment of the weighted observable. Chapter 52 develops the independent-sample variance argument and its tail bounds; here the key point is that the random summand is `L(X)g(X)`, not `g(X)` alone.

At the level of measures, the change-of-measure theorem is not merely a pointwise substitution. One proves that `Q.withDensity L=P` when `L` is the Radon–Nikodym derivative, then applies integral congruence. For indicator observables this says `P(A)=∫_A L dQ`; nonnegative simple functions follow by finite linearity, and general nonnegative observables follow by approximation. This explains why the general proof carries measurability and absolute-continuity hypotheses even when the final formula looks like cancellation of two densities.

## 2. Worked example: a finite target and a uniform proposal

Let the state space be `{0,1,2}`. Suppose the target law is

\[
  P(0)=\frac12,\qquad P(1)=\frac13,\qquad P(2)=\frac16,
\]

and the proposal is uniform, `Q(i)=1/3`. The likelihood ratios are

\[
  L(0)=\frac32,\qquad L(1)=1,\qquad L(2)=\frac12.
\]

For `g=1_{\{0\}}`, one proposal draw contributes `L(X)g(X)`, which is `3/2` when `X=0` and zero otherwise. Its proposal expectation is

\[
  \frac13\cdot\frac32=\frac12=\mathbb{E}_P[g].
\]

The proposal samples state `0` less often than the target does, but its larger weight corrects the frequency exactly in expectation.

On a finite type, no Radon–Nikodym theorem is needed to understand the calculation: expand the integrals as finite sums and cancel `Q(x)` in `Q(x)L(x)`. This is a useful first formalization because it isolates the support condition and makes any division by zero visible.

## 3. Finite weights and support

For probability mass functions `p` and `q` on a finite type, define

\[
  L(x)=\begin{cases}
    p(x)/q(x),&q(x)>0,\\
    0,&q(x)=0.
  \end{cases}
\]

The condition `p(x)>0 → q(x)>0` ensures that no target mass is lost. Then

\[
  \sum_x q(x)L(x)g(x)=\sum_x p(x)g(x).
\]

The proof splits on whether `q(x)=0`. In the positive case, the ratio cancels. In the zero case, the support hypothesis forces `p(x)=0`, so both contributions vanish.

In Lean, state the support condition before defining the weight. It is tempting to use a totalized division operation and let `simp` handle zero denominators, but totalization does not encode the mathematical requirement `P ≪ Q`. A named support lemma explains why the zero branch contributes nothing and can be reused for every observable.

For a finite type, `P ≪ Q` is equivalent to the pointwise implication `q(x)=0 → p(x)=0`. Prove this equivalence once, then use it to move between the measure statement and the coordinate statement. It is especially useful when one theorem is expressed using measures and another using a PMF's point probabilities.

The PMF integration interface is a convenient bridge: for finite types, integrating against a PMF-derived measure becomes a weighted `Finset` sum. For general measures, use the Radon–Nikodym derivative and the integral change-of-measure theorem. The two proofs share the same structure but have different technical obligations.

## 4. Unnormalized targets

Often the target is specified by a nonnegative weight `f` with finite positive normalizer

\[
  Z=\int f\,d\lambda,
  \qquad
  P(dx)=\frac{f(x)}{Z}\,\lambda(dx),
\]

while samples are drawn from a proposal measure `Q` with density `q` relative to `λ`. In a finite discrete model, the importance weight is `f(x)/q(x)`. Then

\[
  \mathbb{E}_Q\left[\frac{f(X)}{q(X)}g(X)\right]
  =\int f(x)g(x)\,d\lambda(x)
  =Z\mathbb{E}_P[g].
\]

If `Z` is known, divide the unbiased weighted estimate by `Z`. If `Z` is unknown, estimate it using the same weights with `g=1`, then take a ratio:

\[
  \widehat I_n^{\mathrm{SN}}
  =\frac{\sum_i W_i g(X_i)}{\sum_i W_i},
  \qquad W_i=\frac{f(X_i)}{q(X_i)}.
\]

This is self-normalized importance sampling. Its ratio cancels the unknown `Z`, but a ratio of unbiased random quantities is not generally unbiased. It is a distinct estimator with a distinct error analysis.

There is also a finite-sample domain condition: if every sampled point has zero target weight, then the denominator vanishes and the ratio is undefined. One can assume the proposal is supported on the positive target set, prove the denominator is positive almost surely, or define a fallback on the zero-denominator event and analyze that modified estimator. A totalized division in Lean should not silently choose which statistical convention is intended.

The formalization should expose the normalization boundary. Prove the exact integral identity for the unnormalized numerator and the identity for the normalizer separately; only then form the ratio, with a proof that its denominator is positive. This avoids mixing a measure-theoretic change of measure with nonlinear division of random variables.

When all weights are multiplied by the same positive constant, the self-normalized estimate is unchanged because that factor cancels from numerator and denominator. This is useful when weights are rescaled to avoid numerical overflow. It does not make the estimator unbiased, and a theorem about scale invariance should not be presented as a probabilistic accuracy guarantee.

## 5. A self-normalized estimator can be biased

Take a two-state target with unnormalized weights `f(0)=9` and `f(1)=1`. Its normalized target probability of state `0` is `9/10`. Let the proposal be uniform on the two states, and estimate the target expectation of `g=1_{\{0\}}` from a single draw using the self-normalized formula.

With one sample, the numerator and denominator contain the same weight, so the estimator equals `g(X₁)`. Its expectation under the uniform proposal is `1/2`, not `9/10`. The estimator is biased even though the weight ratio is correct.

This counterexample is important because algebra can make self-normalization look exact. For a finite sample, the ratio

\[
  \frac{\sum_i W_i g(X_i)}{\sum_i W_i}
\]

is not the ratio of the expectations of its numerator and denominator. To prove asymptotic consistency, use a law of large numbers and show the limiting denominator is nonzero. Do not claim finite-sample unbiasedness from the population change-of-measure identity.

## 6. Weight variability and effective sample size

Importance weights can have very different magnitudes. If a small number of proposal samples carry most of the total weight, the estimator may have high variance even though it remains unbiased. A common diagnostic is

\[
  \mathsf{ESS}=\frac{(\sum_i W_i)^2}{\sum_i W_i^2}.
\]

For equal weights this equals the sample count; when one weight dominates it approaches one. ESS is a statistic of the realized weights, not an exact count of independent samples and not by itself a convergence theorem.

The proposal affects the second moment `E_Q[(Lg)^2]`. A proposal that puts mass where `|g|` and the target density are large can reduce variance; a proposal that is too small in a region of target mass can create enormous weights. For estimating a normalizing constant, the target density itself guides proposal design. For estimating a signed or real-valued integral, the magnitude of the integrand also matters.

In a formal development, prove scale invariance of ESS directly: multiplying every weight by `c>0` multiplies numerator and denominator by `c²`. Then make no stronger probabilistic claim without a variance or concentration theorem. The diagnostic helps inspect finite runs; it does not replace support, integrability, or error assumptions.

### Proposal choice and second moments

For estimating `I=∫h dλ` by drawing from a density `q` relative to `λ`, the unbiased summand is `h(X)/q(X)`. Its second moment is

\[
  \int \frac{h(x)^2}{q(x)}\,d\lambda(x),
\]

when the integral is finite and `q` is positive on the support of `h`. The variance is this second moment minus `I²`. A proposal that assigns too little mass where `|h|` is large can have infinite variance even when the target integral itself is finite.

For nonnegative `h`, choosing `q` proportional to `h` makes the weight constant and gives zero variance for this idealized integral estimate. In practice, that choice is unavailable precisely because the integral is unknown. For signed `h`, the second-moment minimizing density is proportional to `|h|`, under the same support and normalization conditions. Cauchy–Schwarz proves the comparison by applying it to `|h|/√q` and `√q`.

Formalize the second-moment identity before comparing proposals. If `q` may vanish or the space is continuous, make support and integrability explicit; do not use `h²/q` as an ordinary real function until the zero-density branch has been handled.

### Worked example: a proposal can make variance worse

Let the target assign probability `0.9` to state `0` and `0.1` to state `1`, and estimate the target probability of state `1`. If the proposal assigns probabilities `0.99` and `0.01`, the likelihood ratio at state `1` is `10`. The weighted summand is therefore `10` with probability `0.01` and zero otherwise. It is unbiased, but its variance is `0.99`.

Under a uniform proposal, the weight at state `1` is `0.2`; the summand is `0.2` with probability `1/2` and zero otherwise, with variance `0.01`. Both proposals cover the target support, but the uniform proposal gives a much better estimate for this particular observable. This calculation separates correctness from efficiency: support makes the estimator valid, while the second moment measures its quality.

This finite example is well suited to exact rational arithmetic. Prove the expected value and second moment from the two outcomes, then compare the variances. It also demonstrates why a proposal should be assessed relative to the observable being estimated, not only by how close its distribution appears to the target.

## 7. Continuous change of measure

In a general measurable space, represent `P` using its Radon–Nikodym derivative with respect to `Q`. Mathlib's measure-decomposition API provides `rnDeriv`, absolute continuity, and integral identities for changing from one measure to another. A density formulation may instead use `withDensity` and its integral lemmas.

The theorem choice depends on the object. For nonnegative functions, a Lebesgue integral identity often avoids proving finite integrability first. For real or vector-valued Monte Carlo observables, prove the weighted function is integrable under `Q` before using the Bochner integral identity. If only an almost-everywhere equality of densities is available, rewrite under the measure for which that equality holds.

Mathlib's `Measure.withDensity` and `Measure.rnDeriv` interfaces make the density relation explicit; their integral identities then handle expectations. For a PMF, `PMF.integral_eq_sum` turns expectations into finite weighted sums. This gives a useful proof ladder: establish the result for finite PMFs, prove the change-of-measure statement for measures, and specialize the general theorem back to the finite example as a consistency check.

The same boundary appears in Lean's scalar types. PMF masses are naturally nonnegative reals, measures use extended nonnegative reals, and Bochner expectations use real or normed-space values. Convert the density and weight only where an integral theorem requires it. A small lemma that states the finite expectation identity in the chosen scalar type is easier to maintain than repeated coercion chains inside the main proof.

This section is where the finite example stops being a complete proof template. In the finite case, support is a pointwise implication and all sums are finite. In the general case, absolute continuity, measurability of the derivative, and integrability of the weighted observable become explicit hypotheses. The theorem should carry those assumptions instead of hiding them in informal notation such as “divide by the proposal density.”

## 8. A proof workflow

1. Identify the target measure and proposal measure.
2. Prove absolute continuity of target with respect to proposal, or its finite support analogue.
3. Define the likelihood ratio using the Radon–Nikodym derivative or pointwise mass ratio.
4. Prove measurability and integrability of the weighted observable.
5. Apply the change-of-measure identity to establish unbiasedness.
6. If the target is unnormalized, state the numerator and normalizer identities separately.
7. Treat self-normalized estimates as ratios and establish a nonzero denominator.
8. Use second moments or variance bounds for uncertainty; do not infer them from unbiasedness.
9. Keep support checks and zero-density cases visible in finite computations.

## 9. Common failure modes

### The proposal misses target support

If `P` is not absolutely continuous with respect to `Q`, proposal samples cannot represent all target mass.

### A totalized zero denominator is treated as valid importance sampling

Lean division is defined at zero, but the mathematics still requires support or a separate zero-mass argument.

### An unknown normalizer is silently removed

Unnormalized weights estimate an unnormalized integral. Divide by `Z` or use a self-normalized ratio, and state which estimator is meant.

### A ratio estimator is called unbiased

Self-normalized importance sampling is generally biased at finite `n`.

### Integrability is inferred from a finite target expectation

The proposal-weighted random variable needs its own integrability or moment proof.

### ESS is treated as a theorem about independent draws

ESS is a weight diagnostic; it does not certify convergence or effective independence.

## 10. Exercises

1. State the change-of-measure identity for `P ≪ Q` and a nonnegative observable.
2. Derive the finite importance-sampling identity from point masses.
3. List the exact support condition needed for the finite likelihood ratio.
4. Compute the importance weights in the three-state example and verify unbiasedness for the indicator of state `0`.
5. Prove the unnormalized-target identity for a finite proposal.
6. Explain why the self-normalized one-sample estimator in Section 5 is biased.
7. Show ESS is invariant under multiplying all weights by the same positive constant.
8. Identify the integrability condition needed for a real-valued weighted observable.
9. Compare the finite PMF-sum proof with the Radon–Nikodym proof.
10. Locate `PMF.integral_eq_sum` and a Radon–Nikodym change-of-measure theorem in Mathlib's documentation.

## 11. Lean formalization

The first block keeps the initial two-state weighted-sample model. The second block connects the
general theory to Mathlib: nonnegative integrals change measure by the Radon–Nikodym derivative,
real-valued Bochner integrals use its real-valued density, and a finite PMF expectation is a sum over
its point masses. The final rational identities check the three-state example and the finite-sample
bias of the one-draw self-normalized estimator.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def proposal : Weight := uniformWeight
def importanceLikelihood : Weight := fun s => if s = zero then 2 else 1
def weightedSample : Weight := fun s => proposal s * importanceLikelihood s

theorem importanceWeightNormalizer : totalWeight weightedSample = 3 := by decide
theorem weightedMassAtZero : weightedSample zero = 2 := by decide
```

```lean
open MeasureTheory
open scoped ENNReal

theorem exercise_51_1_lintegral_change_of_measure
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) {f : X → ℝ≥0∞} (hf : AEMeasurable f ν) :
    ∫⁻ x, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x, f x ∂μ :=
  MeasureTheory.lintegral_rnDeriv_mul hμν hf

theorem exercise_51_8_real_change_of_measure
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [Measure.HaveLebesgueDecomposition μ ν] [SigmaFinite μ]
    (hμν : μ ≪ ν) {f : X → ℝ} :
    ∫ x, (μ.rnDeriv ν x).toReal * f x ∂ν = ∫ x, f x ∂μ :=
  MeasureTheory.integral_toReal_rnDeriv_mul hμν

theorem exercise_51_10_pmf_expectation_finite_sum
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype X] (p : PMF X) (f : X → ℝ) :
    ∫ x, f x ∂p.toMeasure = ∑ x, (p x).toReal * f x := by
  simpa [smul_eq_mul] using PMF.integral_eq_sum p f

theorem exercise_51_4_three_state_target_normalizes :
    (1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1 := by
  norm_num

theorem exercise_51_4_weighted_indicator_is_unbiased :
    (1 : ℚ) / 3 * ((1 / 2 : ℚ) / (1 / 3)) = 1 / 2 := by
  norm_num

theorem exercise_51_6_one_sample_self_normalized_estimator_is_biased :
    (1 : ℚ) / 2 ≠ 9 / 10 := by
  norm_num
```

## Summary

Importance sampling rewrites a target expectation as a proposal expectation weighted by a Radon–Nikodym derivative. In finite spaces this becomes a pointwise mass ratio, provided the proposal covers the target support. Unnormalized targets lead to unbiased estimates of unnormalized integrals; self-normalization removes the unknown constant but generally introduces finite-sample bias. Support, integrability, and variance are separate obligations that should be formalized separately.

## Further reading

- [Mathlib: Radon–Nikodym derivatives and measure decomposition](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.html)
- [Mathlib: PMF integrals and finite weighted sums](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Integrals.html)
- Chapters 31–34 for measure theory, probability measures, and expectations.
- Chapters 42 and 49 for posterior laws and target-preserving Monte Carlo transitions.
