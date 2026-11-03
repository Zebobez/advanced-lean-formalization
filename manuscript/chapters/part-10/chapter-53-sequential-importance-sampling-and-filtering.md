# Chapter 53 — Sequential Importance Sampling and Filtering

> **Audience.** This chapter assumes familiarity with Markov kernels, Bayesian updating, importance sampling, and finite probability measures. It develops the recursive filtering equation and sequential importance weights for finite hidden-state models.

In a hidden-state model, information arrives one observation at a time. Recomputing the posterior from the entire history at every step is mathematically possible but hides the recursive structure. A filter stores the current state distribution, predicts it through a transition kernel, and reweights the prediction by the new observation likelihood.

Sequential importance sampling approximates this recursion using paths drawn from a proposal process. Each path receives a product of incremental likelihood ratios. The formalization challenge is to keep the observation update, state transition, and proposal correction as separate operations, then compose them in the correct order. Mathlib's measure-kernel composition and posterior interfaces provide useful boundaries; the finite-state recursion below makes the weights and normalizers explicit.

## Learning objectives

By the end of the chapter, you should be able to:

- express a Bayesian filter as prediction followed by likelihood weighting;
- define the unnormalized Feynman–Kac measure and its normalizer;
- derive the incremental importance ratio for a proposal transition;
- factor a path likelihood into sequential weights;
- identify support and zero-normalizer conditions;
- represent kernel composition and measure binding in a Lean development.

## 1. Hidden-state filtering as a recursive update

Let `E_t` be the hidden-state space at time `t`. A Markov kernel `M_{t+1}` describes the transition from `E_t` to `E_{t+1}`. Given an observation `y_{t+1}`, let `G_{t+1}(z)` be its likelihood when the new hidden state is `z`.

Suppose `η_t` is the current posterior distribution of the state. First predict the next state:

\[
  \bar\eta_{t+1}=\eta_t\mathbin{\mathrm{bind}}M_{t+1}.
\]

Then weight the prediction by the observation likelihood and normalize:

\[
  \eta_{t+1}(A)
  =\frac{\int_A G_{t+1}(z)\,d\bar\eta_{t+1}(z)}
         {\int G_{t+1}(z)\,d\bar\eta_{t+1}(z)},
\]

provided the denominator is positive and finite. The denominator is the predictive probability or evidence of the new observation under the current filter.

```text
current filter ηₜ ── transition Mₜ₊₁ ──▶ predicted law η̄ₜ₊₁
                                               │
                                  multiply by likelihood Gₜ₊₁
                                               ▼
                                  normalize by evidence cₜ₊₁
                                               │
                                               ▼
                                         next filter ηₜ₊₁
```

The order matters. The likelihood is evaluated at the post-transition state. If an observation model is instead attached to the pre-transition state, the formula changes and so do the proof obligations. State the timing convention before defining the recursive update.

## 2. Unnormalized Feynman–Kac measures

It is often easier to delay normalization. For a nonnegative measurable test function `f`, define

\[
  \gamma_{t+1}(f)
  =\int \eta_t(dx)\int M_{t+1}(x,dz)
       G_{t+1}(z)f(z).
\]

The evidence increment is `c_{t+1}=γ_{t+1}(1)`, and the normalized filter is

\[
  \eta_{t+1}(f)=\frac{\gamma_{t+1}(f)}{\gamma_{t+1}(1)}.
\]

At the measure level, `γ_{t+1}` is the predicted measure weighted by the potential `G_{t+1}`. Iterating the recursion expresses the unnormalized measure as a composition of transition and potential operators. This is a finite-horizon Feynman–Kac flow.

Separating `γ` from `η` has two benefits. The recursion is linear in the unnormalized measure, which makes induction and composition easier. The normalization constant is recorded explicitly, which is essential for evidence calculations. Normalizing after each step may be convenient computationally, but the proof should preserve the product of incremental normalizers when the marginal likelihood is needed.

If `c_t` denotes the evidence increment at time `t`, repeated substitution gives the sequence evidence as `∏_{t=1}^T c_t`. Prove this identity alongside the normalized recursion by induction on `T`. The base case is the prior; the induction step expands the next weighted measure and uses the previous normalization equation. This is a useful example of a proof where carrying the normalizer as an explicit variable prevents a long algebraic expression from becoming opaque.

If `γ_{t+1}(1)=0`, the observation has zero predictive probability under the model. The normalized posterior is then undefined. A formal definition may totalize the update by returning an arbitrary probability measure in that branch, but the theorem describing the intended posterior must assume positive evidence.

Likelihoods need only be known up to a positive scale to compute the normalized filter. If `G_{t+1}` is replaced by `cG_{t+1}` for `c>0`, the numerator and evidence are both multiplied by `c`, so `η_{t+1}` is unchanged. The evidence itself is multiplied by `c`, however. This is the same normalization distinction seen in Chapters 49 and 51: scale cancels from a normalized law but remains relevant when computing a marginal likelihood.

Over a horizon `T`, the unnormalized path measure has density proportional to

\[
  \eta_0(x_0)\prod_{t=1}^{T}M_t(x_{t-1},x_t)G_t(x_t).
\]

Its total mass is the joint evidence of the observation sequence. Repeated filtering factors that mass into one-step predictive evidences. This factorization is the probabilistic reason that a recursive filter can compute a batch normalizer without storing every past state, even though a smoothing query may still require path information.

## 3. Worked example: one-step binary filtering

Let the hidden state be `E={0,1}` with a uniform prior. Suppose the transition is symmetric with probability `r` of switching states. The predicted distribution remains uniform. An observation has likelihood

\[
  G(0)=\frac14,\qquad G(1)=\frac34.
\]

The evidence is

\[
  c=\frac12\cdot\frac14+\frac12\cdot\frac34=\frac12,
\]

and the updated posterior satisfies

\[
  \eta(1)=\frac{(1/2)(3/4)}{1/2}=\frac34,
  \qquad
  \eta(0)=\frac14.
\]

This example tests every layer: the transition preserves the symmetric prior, the likelihood multiplies point masses, the normalizer is a sum, and the result is a probability measure. If `r` were not symmetric or the prior were nonuniform, the prediction step would have to be computed before applying the same weighting formula.

In Lean, define the transition rows as PMFs or finite probability measures, then calculate the predicted state masses. Keep the evidence as a named rational number. The posterior coordinates follow by exact finite arithmetic, which is simpler than unfolding a general conditional-kernel construction for a two-state example.

### Continue the binary example for a second observation

Take switch probability `r=1/4`, so the transition stays in place with probability `3/4`. After the first observation, the filter is `(1/4,3/4)`. Predicting one more step gives

\[
  \bar\eta_2(1)=\frac14\cdot\frac14+\frac34\cdot\frac34=\frac58,
  \qquad \bar\eta_2(0)=\frac38.
\]

Using the same likelihood `(1/4,3/4)`, the next evidence is

\[
  c_2=\frac38\cdot\frac14+\frac58\cdot\frac34=\frac9{16},
\]

and the updated probability of state `1` is `((5/8)(3/4))/(9/16)=5/6`. The joint evidence for both observations is `c₁c₂=9/32`. This calculation checks both the recursive posterior and the product-of-increments evidence identity.

For formalization, state the one-step update as a function on probability vectors and prove the normalizer identity once. The two-step result is then function composition and rational simplification, not a fresh enumeration of all four hidden-state paths.

## 4. Sequential importance ratios

Exact filtering may be expensive when the state space is large. Let `R_{t+1}(x,·)` be a proposal kernel for drawing a new state `z` from the current state `x`. The target's unnormalized one-step transition-and-observation measure is

\[
  M_{t+1}(x,dz)G_{t+1}(z).
\]

If this measure is absolutely continuous with respect to the proposal row, define the incremental importance weight

\[
  W_{t+1}(x,z)
  =G_{t+1}(z)\frac{dM_{t+1}(x,\cdot)}{dR_{t+1}(x,\cdot)}(z).
\]

In a finite state space with positive proposal entries on the target support, this is

\[
  W_{t+1}(x,z)=G_{t+1}(z)\frac{M_{t+1}(x,z)}{R_{t+1}(x,z)}.
\]

For a path `x₀,…,x_T` sampled from an initial proposal `q₀` and transitions `R_t`, the cumulative weight is

\[
  W_T(x_{0:T})
  =\frac{\eta_0(x_0)}{q_0(x_0)}
    \prod_{t=1}^T
      G_t(x_t)\frac{M_t(x_{t-1},x_t)}{R_t(x_{t-1},x_t)}.
\]

Multiplying the proposal path probability by this weight cancels every proposal factor and recovers the target path weight. This pathwise cancellation is the sequential counterpart of the one-step change-of-measure identity in Chapter 51.

## 5. Worked example: proposal correction along a two-step path

Consider a finite hidden chain with initial law `η₀`, target transitions `M₁,M₂`, and observation likelihoods `G₁,G₂`. If the proposal uses the same transitions, `R₁=M₁` and `R₂=M₂`, the transition ratios cancel and the path weight is simply

\[
  W_2=G_1(x_1)G_2(x_2).
\]

This is the bootstrap proposal. If instead `R_t` favors states likely under the next observation, each transition ratio corrects the change in proposal. For a path with positive proposal probability,

\[
  q_0(x_0)R_1(x_0,x_1)R_2(x_1,x_2)W_2
  =\eta_0(x_0)M_1(x_0,x_1)G_1(x_1)M_2(x_1,x_2)G_2(x_2).
\]

The equality is proved by cancellation in the finite product. If a proposal probability is zero while the right-hand target path weight is positive, the path is missed and importance correction is impossible. The support condition must therefore be stated over entire target paths or proved one transition at a time.

For a formal proof, use induction on the path length. The induction step multiplies the previous path-weight identity by the next proposal transition and incremental weight. This avoids a monolithic product simplification and gives a reusable theorem for any finite horizon.

## 6. Proposal support and zero potentials

At each time, the proposal kernel must cover the weighted target transition. In measure form, require

\[
  M_{t+1}(x,\cdot)G_{t+1}(\cdot)\ll R_{t+1}(x,\cdot)
\]

for relevant current states, with the appropriate almost-everywhere qualification in a general model. In a finite model, every positive target transition with positive observation likelihood must have positive proposal probability.

Zero likelihoods are harmless for the unnormalized update: they remove states from the weighted measure. They may create a zero normalizer if all predicted states have zero likelihood. The filter then has no posterior under the assumed model for that observation. Do not replace this logical failure with an arbitrary fallback posterior unless the API explicitly totalizes the definition and all correctness theorems exclude the zero-evidence branch.

Support conditions also affect numerical stability. Ratios can become large when `R` is small but nonzero where `M G` is substantial. This is a variance problem rather than a correctness problem: absolute continuity gives validity, while second moments determine quality. Chapter 51 treats this distinction in the one-step setting.

## 7. Kernel and measure composition in Mathlib

Mathlib composes kernels with `η ∘ₖ κ`, where `κ` acts first and `η` acts second. Binding a measure and then composing kernels agrees with binding once through the composite. This is the API form of the Chapman–Kolmogorov and prediction recursion.

A likelihood potential is not generally a Markov kernel: weighting a transition by `G` changes its total mass. In a finite model, represent the unnormalized update as a finite measure-valued map or as a weighted kernel, and prove its total mass is the evidence. Do not ask Lean to infer a Markov-kernel instance when the rows are not probability measures before normalization.

When proving equality of filters, decide whether the target is measure equality or equality of integrals against a test class. On finite types, point-mass equality determines the measure and reduces to coordinates. In a general space, the kernel integral identity can be more direct, especially for nonnegative test functions. Use the strongest form required by later results, but do not unfold a measure equality into arbitrary sets if a documented integral characterization already applies.

For Bayesian models, `Kernel.posterior` packages a posterior kernel through disintegration of the joint prior-and-observation measure. That interface is useful when the goal is to prove a conditional law exists or to characterize it almost everywhere. For a concrete finite filter, explicit weighted sums are usually more direct. A good library boundary lets the finite theorem validate the formulas while the posterior API handles the general measurable construction.

## 8. Filtering versus smoothing

Filtering estimates the current hidden state given observations up to the current time. Smoothing estimates a past state using observations that arrived later. The filtering recursion stores a distribution on the current state; smoothing requires additional backward information or a joint path distribution.

This distinction affects both types and theorems. A filter state can be a probability measure on `E_t`; a smoother may be a measure on `E_s × E_t` or a kernel from the current state to an earlier one. If a proof suddenly needs a past state after it has marginalized that state away, the representation may need to retain a joint measure rather than only the filter marginal.

Mathlib's measure-kernel composition and posterior identities can express the joint laws. The algorithmic distinction remains mathematical: future observations change the conditional distribution of the past, while the forward filter is already a sufficient summary for predicting future observations in a Markov model.

### A finite-state representation

On a finite state type, store a filter as a probability vector and a potential as a nonnegative function. Prediction is matrix multiplication; weighting is pointwise multiplication; normalization divides by the sum. A helper theorem can package the update as a partial function requiring a positive denominator, or as a total function with a default branch and a separate success predicate.

The partial form mirrors the mathematics but introduces domain proofs at each update. The total form composes more easily but can conceal an impossible observation if callers ignore the success predicate. Choose based on the downstream theorem: a proof about valid observation sequences should carry positivity, while a data-processing program may need a defined fallback for all inputs.

Finite sums also give a direct proof that the product of incremental evidence values equals the normalizer of the full path likelihood. Prove this by induction using the definition of the unnormalized measure. Keeping that identity as a separate lemma provides a bridge between filtering code and a batch calculation over complete paths.

## 9. A proof workflow

1. State the timing convention for transitions and observations.
2. Define the prediction kernel and likelihood potential.
3. Define the unnormalized update and name its total mass as evidence.
4. Prove evidence is finite and positive before normalizing.
5. For a proposal, establish absolute continuity and define the incremental ratio.
6. Prove the path-weight identity by induction on the horizon.
7. Keep filtering marginals separate from path measures used for smoothing.
8. Use kernel composition for transitions and posterior/disintegration APIs for general conditional laws.
9. Analyze weight variance separately from support correctness.

## 10. Common failure modes

### The likelihood is attached to the wrong time

State whether `G_t` observes the pre-transition or post-transition state.

### Normalization occurs before positivity is proved

An observation with zero evidence has no normalized posterior.

### A weighted kernel is declared Markov

Potential weighting changes total mass. Normalize only after identifying the evidence.

### Proposal ratios are missing a transition direction

The correction is target transition divided by proposal transition, multiplied by the observation likelihood.

### Path support is assumed from the initial distribution alone

Every target transition with positive weighted mass must be covered by the proposal.

### Filtering and smoothing are given the same output type

Filtering returns a current-state marginal; smoothing retains information about past states.

### Large weights are confused with invalid weights

Positive support ratios establish validity; second moments determine variance and stability.

## 11. Exercises

1. Write the predict-then-weight filtering recursion.
2. Define the unnormalized update and its evidence normalizer.
3. Compute the one-step binary posterior in Section 3.
4. Derive the incremental importance ratio for a finite transition model.
5. Prove the two-step path-weight identity in Section 5.
6. State the proposal-support condition for a weighted transition.
7. Explain what zero observation evidence means for the posterior.
8. Distinguish a Markov transition kernel from an unnormalized weighted kernel.
9. Describe the order of Mathlib's kernel composition `η ∘ₖ κ`.
10. Explain why smoothing needs more information than the filtering marginal.
11. Locate the posterior-kernel reconstruction theorem in Mathlib's documentation.

## Summary

Sequential filtering predicts a state distribution through a transition kernel, weights the prediction by an observation likelihood, and normalizes by the evidence. Sequential importance sampling replaces target transitions with proposal transitions and accumulates a product of likelihood ratios. Support makes the change of measure valid; evidence positivity makes normalization valid; second moments determine estimator quality. Kernel composition, posterior kernels, and finite weighted sums provide distinct formal interfaces for these steps.

## Further reading

- [Mathlib: Kernel composition and Chapman–Kolmogorov](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html)
- [Mathlib: Posterior kernels](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Posterior.html)
- Chapters 41–43 for disintegration, posterior updating, and conditional independence.
- Chapters 51–52 for importance weights and Monte Carlo error.

## 12. Lean formalization

The first block retains the integer-weighted finite model used by this
chapter. The next blocks formalize the rational binary filter from Section 3,
its second update, and the algebraic cancellation behind a sequential path
weight. Keeping prediction, weighting, and normalization as named functions
makes the update order visible in the definitions and lets `norm_num` check the
finite calculations exactly.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def firstLikelihood : Weight := fun s => if s = zero then 2 else 1
def secondLikelihood : Weight := fun _ => 1
def sequentialWeight : Weight := fun s => firstLikelihood s * secondLikelihood s

theorem oneStepFilterNormalizer : totalWeight sequentialWeight = 3 := by decide
```

For a `Bool` state, represent a probability distribution by its two rational
point masses. A symmetric transition with switch probability `r` preserves the
uniform law. The posterior update divides the likelihood-weighted mass by its
evidence, so we state the normalizer before using the update.

```lean
def binaryUniformPrior : Bool → ℚ := fun _ => 1 / 2

def binaryObservationLikelihood : Bool → ℚ := fun b =>
  if b then 3 / 4 else 1 / 4

def binarySwitchKernel (r : ℚ) (x z : Bool) : ℚ :=
  if x = z then 1 - r else r

def binaryPredict (μ : Bool → ℚ) (r : ℚ) (z : Bool) : ℚ :=
  μ false * binarySwitchKernel r false z +
    μ true * binarySwitchKernel r true z

def binaryEvidence (μ G : Bool → ℚ) : ℚ :=
  μ false * G false + μ true * G true

def binaryUpdate (μ G : Bool → ℚ) (z : Bool) : ℚ :=
  μ z * G z / binaryEvidence μ G

theorem binary_uniform_prediction (r : ℚ) (z : Bool) :
    binaryPredict binaryUniformPrior r z = 1 / 2 := by
  cases z <;> simp [binaryPredict, binaryUniformPrior, binarySwitchKernel] <;> ring

theorem binary_first_evidence :
    binaryEvidence binaryUniformPrior binaryObservationLikelihood = 1 / 2 := by
  norm_num [binaryEvidence, binaryUniformPrior, binaryObservationLikelihood]

theorem binary_first_posterior_true :
    binaryUpdate binaryUniformPrior binaryObservationLikelihood true = 3 / 4 := by
  norm_num [binaryUpdate, binaryEvidence, binaryUniformPrior,
    binaryObservationLikelihood]

theorem binary_first_posterior_false :
    binaryUpdate binaryUniformPrior binaryObservationLikelihood false = 1 / 4 := by
  norm_num [binaryUpdate, binaryEvidence, binaryUniformPrior,
    binaryObservationLikelihood]
```

The second update predicts the posterior `(1/4, 3/4)` through a transition
with switch probability `1/4`, then applies the same observation likelihood.
These exact equalities check the predicted masses, the next evidence, the
updated posterior, and the product of the two evidence increments.

```lean
def binaryFirstFilter (z : Bool) : ℚ :=
  binaryUpdate binaryUniformPrior binaryObservationLikelihood z

def binarySecondPrediction (z : Bool) : ℚ :=
  binaryPredict binaryFirstFilter (1 / 4) z

def binarySecondEvidence : ℚ :=
  binaryEvidence binarySecondPrediction binaryObservationLikelihood

def binarySecondFilter (z : Bool) : ℚ :=
  binaryUpdate binarySecondPrediction binaryObservationLikelihood z

theorem binary_second_prediction_false :
    binarySecondPrediction false = 3 / 8 := by
  norm_num [binarySecondPrediction, binaryPredict, binaryFirstFilter,
    binaryUpdate, binaryEvidence, binaryUniformPrior,
    binaryObservationLikelihood, binarySwitchKernel]

theorem binary_second_prediction_true :
    binarySecondPrediction true = 5 / 8 := by
  norm_num [binarySecondPrediction, binaryPredict, binaryFirstFilter,
    binaryUpdate, binaryEvidence, binaryUniformPrior,
    binaryObservationLikelihood, binarySwitchKernel]

theorem binary_second_evidence : binarySecondEvidence = 9 / 16 := by
  norm_num [binarySecondEvidence, binaryEvidence, binarySecondPrediction,
    binaryPredict, binaryFirstFilter, binaryUpdate, binaryUniformPrior,
    binaryObservationLikelihood, binarySwitchKernel]

theorem binary_second_posterior_true : binarySecondFilter true = 5 / 6 := by
  norm_num [binarySecondFilter, binaryUpdate, binarySecondEvidence,
    binaryEvidence, binarySecondPrediction, binaryPredict, binaryFirstFilter,
    binaryUniformPrior, binaryObservationLikelihood, binarySwitchKernel]

theorem binary_two_step_evidence :
    (1 / 2 : ℚ) * binarySecondEvidence = 9 / 32 := by
  norm_num [binarySecondEvidence, binaryEvidence, binarySecondPrediction,
    binaryPredict, binaryFirstFilter, binaryUpdate, binaryUniformPrior,
    binaryObservationLikelihood, binarySwitchKernel]
```

Finally, the path identity in Section 5 reduces to cancellation of each
proposal factor. The nonzero assumptions record where the finite ratios are
defined; absolute continuity and support are still model-level obligations
when this algebraic lemma is applied to a family of paths.

```lean
theorem sequential_path_weight_cancels
    (η q₀ r₁ r₂ m₁ m₂ g₁ g₂ : ℚ)
    (hq : q₀ ≠ 0) (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) :
    q₀ * r₁ * r₂ *
      ((η / q₀) * (g₁ * (m₁ / r₁)) * (g₂ * (m₂ / r₂))) =
        η * m₁ * g₁ * m₂ * g₂ := by
  field_simp [hq, hr₁, hr₂]
```
