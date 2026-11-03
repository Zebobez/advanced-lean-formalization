# Chapter 52 — Variance and Monte Carlo Error Bounds

> **Audience.** This chapter assumes familiarity with expectation, independence, L² integrability, and finite product measures. It develops the variance of sample averages and Chebyshev error bounds for Monte Carlo estimates.

An unbiased estimate can still be unreliable if its variance is large. For independent samples with finite second moments, variance quantifies the error of the sample average, and Chebyshev's inequality converts that variance into a finite-sample probability bound. These are useful theorems to formalize because they expose exactly which independence and integrability assumptions justify the familiar `1/n` error scale.

Mathlib defines real-valued variance and extended nonnegative variance, proves additivity for independent sums, supplies Chebyshev's inequality, and bounds variance for almost-everywhere bounded variables. The proof strategy is modular: prove the estimator's expectation, calculate its variance from independence, then apply a tail inequality. Unbiasedness alone does not imply a concentration bound.

## Learning objectives

By the end of the chapter, you should be able to:

- prove a sample average is unbiased;
- derive the `1/n` variance reduction for independent identically distributed samples;
- apply Chebyshev's inequality to obtain a confidence guarantee;
- use boundedness to obtain a variance-only sample-size estimate;
- explain why dependent Markov-chain samples need a different variance calculation;
- organize the Lean proof around `MemLp`, independence, variance, and measure inequalities.

## 1. The sample-average estimator

Let `X₁,…,Xₙ` be independent real-valued random variables with a common expectation `μ` and common variance `σ²`. The sample average is

\[
  \overline X_n=\frac1n\sum_{i=1}^n X_i.
\]

Linearity of expectation gives

\[
  \mathbb{E}[\overline X_n]=\mu,
\]

so the estimator is unbiased. If each variable is square-integrable, independence gives zero covariance between distinct samples, and

\[
  \operatorname{Var}\left(\sum_{i=1}^nX_i\right)
  =\sum_{i=1}^n\operatorname{Var}(X_i)=n\sigma^2.
\]

Scaling variance by `(1/n)^2` yields

\[
  \operatorname{Var}(\overline X_n)=\frac{\sigma^2}{n}.
\]

The `1/n` rate depends on independence. Equal marginal distributions alone do not make the covariance terms vanish.

Identical distributions are not required for the variance calculation. For independent variables with variances `σ_i²`,

\[
  \operatorname{Var}(\overline X_n)=\frac1{n^2}\sum_{i=1}^nσ_i^2,
  \qquad
  \mathbb{E}[\overline X_n]=\frac1n\sum_{i=1}^n\mathbb{E}[X_i].
\]

This version is useful for stratified sampling or for estimators that combine independent samples from different proposals. To estimate a common target without bias, choose weights so the average of the individual expectations equals that target.

## 2. Formalizing independence and variance additivity

Mathlib's `ProbabilityTheory.variance` is the real-valued variance and is defined by converting an extended nonnegative variance to `ℝ`. For the usual finite-variance algebra, establish `MemLp X 2 μ`. The extended version `evariance` is useful when one wants a theorem that remains meaningful before proving finite second moment.

The library theorem `ProbabilityTheory.IndepFun.variance_sum` states that the variance of a finite sum of pairwise independent L² random variables is the sum of their variances. For an iid family, the proof has two obligations:

1. every pair of distinct coordinates is independent;
2. every coordinate has the same variance as the one-sample observable.

On a product probability space, independence comes from the coordinate projections. On an abstract sample space, it is a hypothesis. Do not use a product-space convenience theorem if the random variables are only known to be uncorrelated; pairwise independence is stronger than zero covariance, though zero covariance would suffice for the variance expansion.

After the sum variance is established, apply the variance scaling theorem to the scalar factor `1/n`. Keep `n>0` explicit so the mathematical average and Lean's totalized inverse agree. A short helper theorem for the variance of a normalized sum can then hide conversions between `Finset.sum`, scalar multiplication, and the `variance` definition.

### Finite PMFs and real-valued expectations

For a finite type, `PMF.integral_eq_sum` rewrites expectation as a finite sum weighted by point probabilities. This is convenient for computing the mean and variance of a single sample, while `IndepFun.variance_sum` handles the sample index without expanding the entire product distribution. Use the finite formula for the one-coordinate calculation and the abstract independence theorem for scaling to general `n`.

Mathlib's `variance` is real-valued, while `evariance` lives in `ℝ≥0∞`. The real definition is set to zero when the variance is infinite, so a theorem intended to describe a finite statistical variance should carry an L² hypothesis. If that hypothesis is unavailable, formulate the result with `evariance` and use the extended Chebyshev bound. This choice belongs in the theorem statement, not as a late cast inserted only to make Lean elaborate.

When applying Chebyshev, the probability is also an extended nonnegative real. Convert a real upper bound to `ENNReal` only after proving it is nonnegative. Keeping the variance calculation over `ℝ` and the measure inequality over `ℝ≥0∞` in separate lemmas makes the coercion boundary easy to inspect.

## 3. Worked example: Bernoulli sampling

Let `X_i` be iid Bernoulli random variables with success probability `p`. Each has mean `p` and variance `p(1-p)`. Therefore

\[
  \mathbb{E}[\overline X_n]=p,
  \qquad
  \operatorname{Var}(\overline X_n)=\frac{p(1-p)}{n}.
\]

The estimator `\overline X_n` estimates the probability of success by the observed fraction of successes. Its exact variance is largest at `p=1/2` and vanishes at the deterministic endpoints `p=0` and `p=1`.

For `p=1/4`, the variance is `3/(16n)`. The general variance formula can be proved without expanding every outcome of the `n`-fold product space: apply variance additivity to the coordinate indicators, then scale the sum. This illustrates the value of using the probability API to avoid an exponential case split over sample strings.

For a finite sample type such as `Fin n → Bool`, a second proof can compute the product PMF directly. The direct calculation is a good validation example for small `n`; the independence proof is the scalable argument.

The sample index should be part of the type. A family `X : Fin n → Ω → ℝ` makes the finite sum and its range explicit, while the product measure or independence hypotheses describe how its coordinates are distributed. This representation keeps the estimator's length visible in the theorem statement and avoids encoding a random sample as an informal list with hidden length invariants.

## 4. Chebyshev turns variance into an error probability

For any `ε>0`, Chebyshev's inequality gives

\[
  \mathbb{P}\bigl(|\overline X_n-\mu|\geq\varepsilon\bigr)
  \leq \frac{\operatorname{Var}(\overline X_n)}{\varepsilon^2}
  =\frac{\sigma^2}{n\varepsilon^2}.
\]

Thus, for a desired failure probability `δ>0`, it is sufficient to choose

\[
  n\geq\frac{\sigma^2}{\delta\varepsilon^2}
\]

to guarantee that the probability of error at least `ε` is no more than `δ`. In an actual finite-sample theorem, round the right side up to a natural number and retain the strict positivity conditions needed for the divisions.

Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq` states Chebyshev's inequality for a finite measure and an L² random variable. It returns a measure bound in `ℝ≥0∞`, so translating the real-valued variance estimate into that inequality requires nonnegativity and `ENNReal.ofReal` bookkeeping. If the available hypotheses give only almost-everywhere measurability and an extended variance, use the extended-variance version instead.

Chebyshev is intentionally general and often loose. It uses only a second moment and applies without boundedness or exponential moments. A sharper tail estimate requires additional structure and a theorem that matches that structure; the existence of an unbiased estimator is not enough.

## 5. Worked bound for a Bernoulli mean

For the Bernoulli estimator, Chebyshev yields

\[
  \mathbb{P}(|\overline X_n-p|\geq\varepsilon)
  \leq\frac{p(1-p)}{n\varepsilon^2}
  \leq\frac{1}{4n\varepsilon^2}.
\]

The last inequality uses `p(1-p)≤1/4`. To guarantee failure probability at most `0.05` and error at most `0.1`, this bound asks for `n≥500`. The number is conservative; the purpose is to obtain a theorem from only the range and variance assumptions.

In Lean, separate the symbolic proof from the numerical substitution. First prove the bound for general `p`, `n`, and `ε`, using positivity hypotheses. Then instantiate the values and let arithmetic automation handle the rational comparison. This keeps the probability argument independent of one selected confidence target.

The error event can be written with `≤` at the threshold to match the library theorem. If a user-facing claim uses strict `>` instead, prove the event inclusion explicitly. Boundary conventions matter when turning measure bounds into statements about confidence levels.

To derive a natural-number sample size, avoid putting logarithms into the probability proof. First prove the real inequality under a hypothesis such as `σ²/(n ε²)≤δ`. Then choose `n` large enough using an integer ceiling lemma. This separation keeps the probabilistic theorem stable if a later application changes its numerical tolerance.

The resulting confidence statement is one-sided in its logic: a probability upper bound of `δ` gives confidence at least `1-δ` for the event `|\overline X_n-μ|<ε`. It does not assert that the realized estimate is within `ε` with certainty, and it does not make `δ` an exact failure probability.

In Lean, formulate the bad event as a measurable set and apply the measure bound to that set. Then use complement probability only if the desired statement is phrased as a success event. For finite sample spaces, measurability is often automatic under the discrete measurable structure; for general spaces, establish measurability of the estimator and its absolute-deviation event before invoking Chebyshev.

## 6. Bounded observations give a uniform variance estimate

If `a≤X≤b` almost everywhere, Mathlib proves

\[
  \operatorname{Var}(X)\leq\left(\frac{b-a}{2}\right)^2.
\]

For iid bounded samples in `[a,b]`, this gives

\[
  \mathbb{P}(|\overline X_n-\mu|\geq\varepsilon)
  \leq\frac{(b-a)^2}{4n\varepsilon^2}.
\]

The bound no longer depends on the unknown mean or variance. It is useful when only a range constraint is available. The same structure applies to Monte Carlo integration of a bounded function: take `X_i=g(Z_i)` for independent draws `Z_i` and bound the range of `g`.

There are two proof routes. One can first prove the one-sample variance bound and then use the exact `1/n` variance identity. Alternatively, use a direct variance theorem for the sample average if one is available and its assumptions match. The first route exposes the role of independence and is easier to reuse with different boundedness hypotheses.

## 7. Bias and variance are separate error sources

For any estimator `T` of a real quantity `θ` with finite second moment,

\[
  \mathbb{E}[(T-\theta)^2]
  =\operatorname{Var}(T)+\bigl(\mathbb{E}[T]-\theta\bigr)^2.
\]

The first term is variance; the second is squared bias. An unbiased estimator makes the second term zero but can still have large variance. A self-normalized importance estimator from Chapter 51 may have finite-sample bias, so a variance-only analysis does not control its full mean-squared error.

Formalize this decomposition before applying it to a specific estimator. It is an algebraic identity after inserting and subtracting `E[T]`, but it requires enough integrability to define the second moment. This is another place to state `MemLp T 2 μ` once and reuse it rather than repeatedly unfolding the integral definitions.

## 8. Control variates as a variance-reduction method

Suppose `G` is the observable of interest and `H` is another observable whose expectation is known. For a scalar `β`, define

\[
  G_\beta=G-\beta(H-\mathbb{E}H).
\]

Its expectation remains `E[G]`, so the estimator is unbiased, while its variance is

\[
  \operatorname{Var}(G_\beta)
  =\operatorname{Var}(G)-2\beta\operatorname{Cov}(G,H)
    +\beta^2\operatorname{Var}(H).
\]

When `Var(H)>0`, the minimizing coefficient is `β=Cov(G,H)/Var(H)`. The best variance is smaller when `G` and `H` are strongly correlated. This method can be formalized from the covariance expansion and nonnegativity of a square; it does not require a new probability construction.

For a finite probability space, prove the identity by expanding the finite sums. For general random variables, establish L² integrability of both `G` and `H` and use the variance and covariance identities. The coefficient may be selected from a theoretical covariance or estimated from samples; using an estimated coefficient changes the finite-sample analysis and should be stated separately.

### Worked example: removing a known component

Let `U` and `V` be independent centered variables with variance one. Suppose the quantity of interest is `G=U+V`, and `E[U]=0` is known. Choose the control `H=U`. Then

\[
  G_\beta=U+V-\beta U=(1-\beta)U+V.
\]

Its variance is `(1-β)²+1`, minimized at `β=1`, where the residual is `V` and the variance falls from `2` to `1`. The expectation remains zero throughout. This exact example isolates the mechanism: the control removes a component correlated with the target observable while preserving its expectation.

In a Lean proof, use independence to eliminate the cross term in the variance of the sum, then reduce the remaining polynomial in `β` to a square. The argument does not require estimating `β` from data; that more practical variant introduces additional random dependence and needs its own analysis.

## 9. Why Markov-chain samples need another argument

The sample-average variance identity in Section 1 assumes independent samples. A stationary Markov chain produces dependent observations. The variance expansion then contains covariance terms:

\[
  \operatorname{Var}\left(\frac1n\sum_{i=1}^nG(X_i)\right)
  =\frac1{n^2}\left(n\operatorname{Var}(G(X_1))
    +2\sum_{1\leq i<j\leq n}\operatorname{Cov}(G(X_i),G(X_j))\right).
\]

Stationarity makes these covariances depend on time separation, but does not make them zero. Mixing or spectral estimates can control their sum and lead to an asymptotic variance or a nonasymptotic bound. Chapters 48–50 establish transition convergence and MCMC correctness; a finite-sample error theorem for a Markov-chain average needs this additional dependence analysis.

This distinction catches a common formal error. An invariant marginal law does not provide independence across time. To use `IndepFun.variance_sum`, either prove coordinate independence for fresh samples or use a theorem that explicitly accounts for the Markov dependence.

## 10. Proof workflow

1. Define the estimator as a finite sum or integral of random variables.
2. Prove integrability and, for variance, L² membership.
3. Establish unbiasedness using linearity of expectation.
4. Prove pairwise independence or state the required dependence structure.
5. Apply variance additivity and scalar variance rules.
6. Apply Chebyshev with a positive error threshold.
7. Convert the measure inequality to the desired real or `ENNReal` form.
8. For bounded observations, prove the almost-everywhere range before using the variance bound.
9. If the estimator is biased or samples are dependent, include those terms explicitly.

## 11. Common failure modes

### Unbiasedness is treated as a concentration result

Unbiasedness gives the expectation, not a tail probability. Supply a variance or stronger moment estimate.

### Independence is omitted from the variance sum

Dependent variables contribute covariance terms.

### L² integrability is assumed from measurability

Chebyshev and finite variance calculations require second moments.

### The sample-average scaling is squared incorrectly

Variance scales by the square of a scalar: `Var(cX)=c² Var(X)`.

### The probability convention at the threshold changes

The theorem may bound `ε≤|X-E X|`; translate strict events with an inclusion.

### A Markov chain is treated as iid after burn-in

Discarding initial steps does not prove the remaining observations are independent.

### A variance bound is presented as a sharp confidence interval

Chebyshev is valid under weak assumptions but can be conservative.

## 12. Exercises

1. Prove the sample average of iid integrable variables is unbiased.
2. Derive its variance from pairwise independence and common variance.
3. State the L² assumption needed to apply the variance theorem.
4. Apply Chebyshev to obtain a failure-probability bound for a sample mean.
5. Derive the bounded-range estimate using `variance_le_sq_of_bounded`.
6. Compute the Bernoulli sample-mean variance for parameter `p`.
7. Prove the mean-squared-error decomposition into variance and squared bias.
8. Derive the control-variate variance formula and minimizing coefficient.
9. Explain why a stationary Markov chain does not satisfy the iid variance formula.
10. Locate `IndepFun.variance_sum` and `meas_ge_le_variance_div_sq` in the Mathlib documentation.

## 13. Lean formalization

The initial block preserves the finite two-state calculation. The general statements that follow
use Mathlib's L² and independence hypotheses to derive variance additivity, then record the square
scaling rule, Chebyshev's deviation bound, and the bounded-range estimate. The rational calculation
checks how a one-sample variance of `1/4` scales for an average of two independent samples.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def centeredSample : State → Int := fun s => if s = zero then -1 else 1
def squaredSample (s : State) : Int := centeredSample s * centeredSample s

theorem bernoulliSampleHasZeroMean :
    expectationNumerator uniformWeight centeredSample = 0 := by decide

theorem bernoulliSampleHasSecondMomentTwo :
    expectationNumerator uniformWeight squaredSample = 2 := by decide
```

```lean
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

theorem exercise_52_2_independent_sum_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hXY : X ⟂ᵢ[μ] Y) :
    variance (fun ω => X ω + Y ω) μ = variance X μ + variance Y μ :=
  hXY.variance_fun_add hX hY

theorem exercise_52_2_variance_scales_quadratically
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ) :
    variance (fun ω => c * X ω) μ = c ^ 2 * variance X μ :=
  variance_const_mul c X μ

theorem exercise_52_4_chebyshev
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |X ω - μ[X]|} ≤
      ENNReal.ofReal (variance X μ / ε ^ 2) :=
  meas_ge_le_variance_div_sq hX hε

theorem exercise_52_5_bounded_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hRange : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ ((b - a) / 2) ^ 2 :=
  variance_le_sq_of_bounded hRange hX

theorem exercise_52_6_fair_bernoulli_variance :
    (1 : ℚ) / 2 * (1 - 1 / 2) = 1 / 4 := by
  norm_num

theorem exercise_52_6_two_sample_average_variance :
    (1 : ℚ) / 4 / 2 = 1 / 8 := by
  norm_num
```

## Summary

For iid square-integrable samples, the sample mean is unbiased and its variance is the one-sample variance divided by the sample count. Chebyshev converts that variance into a finite-sample error probability; boundedness gives a uniform variance estimate. Bias, variance, independence, and integrability must be tracked separately. Markov-chain samples are dependent, so their error bounds require covariance, mixing, or spectral arguments beyond the iid calculation.

## Further reading

- [Mathlib: Variance and Chebyshev's inequality](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Variance.html)
- [Mathlib: PMF expectations as finite sums](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Integrals.html)
- Chapters 35–38 for conditional expectation, martingales, and convergence.
- Chapter 51 for importance-weighted estimators and their support conditions.
