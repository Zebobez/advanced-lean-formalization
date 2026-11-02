# Chapter 42 — Bayesian Updating and Posterior Kernels

> **Audience.** This chapter assumes familiarity with probability kernels, disintegration, finite measures, and Radon–Nikodym derivatives. It develops Bayesian updating as construction of a posterior kernel from a prior measure and a likelihood kernel.

Bayesian inference combines a prior distribution on parameters with a model for observed data. Given a parameter, the likelihood kernel describes how data are generated. Once data are observed, a posterior distribution describes uncertainty about the parameter. The formal construction is not merely a formula involving densities: it is a conditional kernel obtained by disintegrating the joint parameter-data measure.

This viewpoint handles discrete, continuous, and mixed models with the same interface. In finite models, the familiar Bayes ratio appears by evaluating the disintegration identity on atoms of positive evidence probability. In general spaces, the posterior is a measurable kernel defined up to almost-everywhere equality under the data marginal.

Mathlib's `posterior κ μ` packages this construction. The main theorem says that combining the data marginal with the posterior reconstructs the joint model after swapping coordinate order. The theorem is a measure-level Bayes rule and is the reliable starting point for formal calculations.

## Learning objectives

By the end of the chapter, you should be able to:

- model a prior and likelihood using a finite measure and a kernel;
- identify the evidence distribution and joint parameter-data law;
- understand `posterior κ μ` through its reconstruction property;
- derive the finite Bayes formula at observations of positive evidence mass;
- explain why posterior values on null evidence are version-dependent;
- use posterior composition to express sequential updating.

## 1. The prior and likelihood model

Let `Ω` be a parameter space and `𝓧` a data space. A prior measure `μ` describes the initial uncertainty about the parameter. A likelihood kernel `κ : Kernel Ω 𝓧` assigns to each parameter `ω` a measure `κ ω` on the data space. For a probabilistic model, `κ` is a Markov kernel: each `κ ω` is a probability measure.

The joint parameter-data measure is the comp-product

\[
  \mu\otimes_m\kappa,
\]

which first draws a parameter according to `μ` and then draws data from `κ ω`. The evidence distribution, also called the prior predictive distribution, is

\[
  \nu=\kappa\circ_m\mu.
\]

It is the marginal law of the data before observing a particular outcome.

```text
parameter ω ── prior μ ──▶ likelihood κ ω ──▶ data x
      │                                            │
      └──── joint measure μ ⊗ₘ κ                   └── marginal ν=κ ∘ₘ μ
                                                       │
                                                       ▼
                                              posterior κ†μ at x
```

The prior and likelihood need not be probability-normalized in the most general API: Mathlib's posterior construction is stated for finite measures and finite kernels. Statistical applications typically use probability priors and Markov kernels, which are special cases of those assumptions.

## 2. The posterior as a conditional kernel

The posterior is a kernel from data to parameters:

\[
  \kappa^\dagger\mu : \mathrm{Kernel}(\mathcal{X},\Omega).
\]

For each observation `x`, it gives a measure on possible parameters. Mathlib defines this as `ProbabilityTheory.posterior κ μ`, with notation `κ†μ`. The construction is the conditional kernel of the swapped joint measure, so it is an instance of Chapter 41's disintegration interface.

The defining Bayes identity is

\[
  (\kappa\circ_m\mu)\otimes_m(\kappa^\dagger\mu)
  =(\mu\otimes_m\kappa).\mathrm{map}(\mathrm{Prod.swap}).
\]

The left-hand side first samples data from the evidence marginal and then parameters from the posterior. The right-hand side is the original joint model with coordinates reordered. This is stronger and more stable than a pointwise equation for densities: it holds as a measure identity and does not require choosing reference densities.

The posterior theorem requires the parameter space to carry a standard Borel structure and be nonempty, the prior measure to be finite, and the likelihood kernel to be finite. These assumptions ensure that the swapped joint measure admits a conditional kernel. If the likelihood is Markov, the posterior is also a probability kernel under the theorem's assumptions.

## 3. Worked example: a binary parameter

Let the parameter be `θ ∈ {0,1}` with prior probabilities

\[
  P(\theta=1)=\frac13,\qquad P(\theta=0)=\frac23.
\]

Suppose the data is a binary observation `x ∈ {0,1}` and

\[
  P(x=1\mid\theta=1)=\frac34,\qquad
  P(x=1\mid\theta=0)=\frac14.
\]

The evidence probability of observing `1` is

\[
  P(x=1)=\frac13\cdot\frac34+\frac23\cdot\frac14
        =\frac14+\frac16=\frac5{12}.
\]

For this positive-mass observation, Bayes' formula gives

\[
  P(\theta=1\mid x=1)
  =\frac{(1/3)(3/4)}{5/12}=\frac35.
\]

The posterior has increased the probability of `θ=1` from `1/3` to `3/5` because the observed data was more likely under that parameter.

For the observation `x=0`, the evidence probability is `7/12`, and the posterior is

\[
  P(\theta=1\mid x=0)=\frac{(1/3)(1/4)}{7/12}=\frac17.
\]

The posterior probabilities over `θ=0` and `θ=1` sum to one for either observation. In a formal proof, this normalization is a useful check that the prior row and likelihood kernel were constructed with the intended weights.

In Lean, represent both finite spaces with discrete measurable structures. Define the prior as a probability measure and the likelihood as a kernel whose two rows are Bernoulli measures. The posterior construction supplies a kernel from observations to parameters. To derive the numeric result, use the measure reconstruction identity on singleton rectangles and simplify the positive evidence denominator. This approach checks the model and Bayes calculation against the same general theorem.

## 4. The finite Bayes formula from disintegration

Suppose both parameter and data spaces are finite, and let `x` be an observation with positive evidence probability. Applying the reconstruction identity to `{x} × {θ}` yields

\[
  \nu(\{x\})\,\kappa^\dagger\mu(x)(\{\theta\})
  =\mu(\{\theta\})\,\kappa(\theta)(\{x\}).
\]

Since `ν {x} ≠ 0`, division gives

\[
  \kappa^\dagger\mu(x)(\{\theta\})
  =\frac{\mu(\{\theta\})\,\kappa(\theta)(\{x\})}
         {(\kappa\circ_m\mu)(\{x\})}.
\]

The denominator is the evidence probability, the numerator is prior mass times likelihood, and the result is the posterior mass. This derivation is not an extra axiom of the posterior API; it follows from the joint-law reconstruction property.

For countable parameter spaces, Mathlib also relates the posterior to a Radon–Nikodym derivative. `posterior_eq_withDensity_of_countable` expresses the posterior as the prior weighted by the likelihood density relative to the evidence distribution, almost everywhere in the data. In a discrete data space, that derivative reduces to the ratio of point probabilities when the evidence atom has positive mass.

The density theorem requires countability of the parameter space and the finite-measure conditions in its signature. In a general uncountable parameter space, the likelihood may not be absolutely continuous with respect to a common evidence measure pointwise in the parameter. The kernel posterior remains available even when a simple density formula does not.

For continuous models with densities relative to a reference measure, the usual analytic Bayes formula is another expression of this construction: multiply the prior density by the likelihood density and normalize by the evidence density. The denominator must be positive at the observation, and the resulting formula is typically an almost-everywhere identity. The kernel theorem is preferable when densities are unavailable or when the model mixes discrete and continuous components.

## 5. Null evidence and versions

If an observation `x` has zero probability under the evidence distribution, the joint law places no mass above that observation. The reconstruction identity therefore does not determine the posterior at `x`. Mathlib's posterior is a total kernel, so a value exists, but different versions can disagree on an evidence-null set while representing the same conditional distribution.

This is not a defect in the definition. No experiment governed by the model observes an evidence-null event with positive probability, and the posterior is characterized only up to almost-everywhere equality under `κ ∘ₘ μ`. A pointwise theorem should include a positive-evidence hypothesis if it uses a ratio formula.

In finite Bayes calculations, split the zero and positive evidence cases before dividing. On the zero case, the numerator for every parameter must also vanish when the model is nonnegative, but the posterior row is not determined by the ratio. A total definition may choose a default row; do not interpret that convention as an empirical inference.

The exceptional set should be measured under the evidence law, not under the prior. The posterior's input is data, so its almost-everywhere statements live on the data space. When transporting an equality through another kernel, check which bind or pushforward produced the measure in the filter; the prior and evidence measures govern different variables.

## 6. Sequential updating and posterior composition

Suppose data arrive in two stages. The first likelihood kernel `κ` maps parameters `Ω` to initial data `𝓧`; a second kernel `η` maps `𝓧` to later data `𝓨`. Their composition `η ∘ₖ κ` is the joint observation model from parameters to final data after integrating over the intermediate observation.

The posterior for the composite model agrees almost everywhere with two updates composed in reverse order: first infer the intermediate data from the final observation using the posterior of `η`, then infer parameters from the intermediate data using the posterior of `κ`. Mathlib states this as `posterior_comp`, with the appropriate evidence marginal in the almost-everywhere filter.

This formula captures sequential Bayesian updating. Its direction is easy to misread: forward models compose from parameters to observations, while posterior kernels move backward from observations to parameters. Check the source and target types at every step. If the data-stage kernel is not Markov or the spaces do not satisfy the posterior hypotheses, the composition theorem may require additional finite-kernel assumptions.

The posterior of an identity kernel is the identity kernel almost everywhere. This is a useful boundary case: observing the parameter itself reveals it, up to the version convention on prior-null states. Another useful identity is `posterior_comp_self`: for a Markov likelihood, drawing data from the prior predictive law and then drawing a parameter from the posterior recovers the prior distribution.

## 7. Worked example: deterministic observations

Let `f : Ω → 𝓧` be a measurable deterministic observation, represented by the kernel that assigns the Dirac measure at `f ω` to parameter `ω`. Given an observation `x`, the posterior is the prior conditioned on the fiber `{ω | f ω = x}` whenever that fiber has positive evidence mass.

If `f` is injective, the data identifies the parameter uniquely, and the posterior is a Dirac measure at the inverse image on observations in the range. If `f` is many-to-one, the posterior redistributes prior mass among all parameters in the observed fiber. For a finite fiber, its weight is proportional to the prior mass of each parameter.

This example shows why posterior inference is not always “recover the parameter.” Data may discard information. The deterministic-kernel posterior identity describes exactly what remains identifiable and avoids pretending that `f` has an inverse when it does not.

## 8. Verifying a candidate posterior

In a finite model, it can be simpler to define posterior rows directly from Bayes' formula than to use the abstract construction. To connect a candidate `η : Kernel 𝓧 Ω` to `posterior κ μ`, prove the joint reconstruction identity

\[
  (\kappa\circ_m\mu)\otimes_m\eta
  =(\mu\otimes_m\kappa).\mathrm{map}(\mathrm{Prod.swap}).
\]

Then apply `ae_eq_posterior_of_compProd_eq` or its coordinate-swapped variant to conclude that `η` agrees almost everywhere with Mathlib's posterior. In finite spaces, the reconstruction proof reduces to checking every pair of atoms. In a countable model, it can be proved by summing the pointwise Bayes identity over measurable subsets.

This route keeps a hand-derived formula from becoming an independent definition of conditional probability. The candidate is accepted because it reconstructs the same joint law. The same method works for any proposed conditional kernel, not just a posterior: prove the comp-product equation, then use uniqueness.

For a continuous candidate based on densities, verify the density normalization and the joint identity under the data marginal. Do not divide through by the evidence density until its positivity or almost-everywhere nonzero property has been established. This is often the key analytic lemma in an otherwise routine posterior proof.

In Lean, keep the candidate kernel's finiteness and measurability facts separate from the reconstruction equality. The uniqueness theorem expects a finite kernel in its hypotheses, and the standard Borel and nonempty instances belong to the parameter space. Once these are supplied, the final conclusion is an almost-everywhere equality under the evidence measure. Stating the intermediate facts explicitly makes the proof resilient if the formula is later generalized from a finite model to a countable one.

## 9. A proof workflow

1. Choose a measurable parameter space and a data space.
2. Define a finite prior measure and a finite likelihood kernel; install probability assumptions when available.
3. Form the evidence measure with `κ ∘ₘ μ` and the joint measure with `μ ⊗ₘ κ`.
4. Use `posterior κ μ` for the conditional kernel from data back to parameters.
5. Apply `compProd_posterior_eq_swap_comp` or an equivalent reconstruction theorem.
6. For discrete formulas, evaluate on singleton rectangles and prove the evidence mass is nonzero before dividing.
7. For countable parameter spaces, use the density theorem when a Radon–Nikodym formula is useful.
8. For sequential observations, compose likelihoods forward and posterior kernels backward.
9. State equalities of posterior kernels almost everywhere under the evidence law.

This workflow keeps Bayes' rule anchored to the joint model. It also makes it easier to detect whether a desired result is about a posterior distribution, an evidence probability, or a pointwise density.

## 10. Common failure modes

### The posterior is treated as a pointwise inverse

A kernel can lose information. The posterior is a conditional distribution and may remain spread across multiple parameter values.

### Bayes' ratio is used with zero evidence

Division requires positive evidence mass or density. On null observations, the posterior version is not determined by the joint law.

### The likelihood is not measurable in the parameter

A row of probability measures is not automatically a kernel. Prove the measurable-dependence property.

### Finiteness and standard Borel assumptions are omitted

The posterior construction requires a finite prior, finite kernel, and a nonempty standard Borel parameter space. Confirm the exact theorem context.

### Coordinate order is confused

The prior joint law is on parameter × data; the posterior law is data × parameter. Use `Prod.swap` explicitly.

### Equality is demanded on null data

The posterior is unique only almost everywhere with respect to the evidence measure. Keep the marginal in the equality statement.

## 11. Exercises

1. Define the evidence measure and joint parameter-data measure from a prior and likelihood kernel.
2. State the reconstruction identity that characterizes `posterior κ μ`.
3. Compute the evidence probability and posterior in the binary example.
4. Derive the singleton Bayes formula from the joint measure identity.
5. Explain why a zero-evidence observation has no uniquely determined posterior row.
6. Describe the countable-parameter Radon–Nikodym formula in words.
7. State how posterior kernels compose for a two-stage observation model.
8. Explain what posterior inference does for a deterministic many-to-one observation.
9. Locate `posterior_comp_self` and identify why it requires a Markov likelihood.
10. List the standard Borel, finiteness, and nonemptiness assumptions of `posterior` in the current Mathlib API.

## Summary

Bayesian updating is disintegration of the joint law formed by a prior and a likelihood kernel. The evidence marginal combined with the posterior reconstructs the swapped joint distribution. In finite spaces, this identity gives the usual Bayes ratio at observations of positive evidence mass; on null observations, posterior values are version-dependent. Mathlib also supports countable-parameter density formulas and composition of sequential posterior updates.

## Further reading

- [Mathlib: Posterior kernels](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Posterior.html)
- [Mathlib: Standard Borel disintegration](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Disintegration/StandardBorel.html)
- [Mathlib: Conditional kernels and reconstruction](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Disintegration/Basic.html)
