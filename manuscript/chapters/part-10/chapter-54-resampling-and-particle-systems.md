# Chapter 54 — Resampling and Particle Systems

> **Audience.** This chapter assumes familiarity with sequential importance sampling, finite PMFs, conditional expectation, and variance. It develops multinomial resampling as a finite random transformation of a weighted particle population.

A sequential particle method replaces an intractable probability distribution with a finite population of weighted states. Propagation moves particles through a transition kernel; weighting scores them against new observations; resampling selects ancestors so the next population has equal weights. Each operation has a separate probabilistic meaning, and a useful formalization proves its properties separately before composing the full filter.

This chapter focuses on multinomial resampling, whose ancestor indices are conditionally independent draws from the normalized weights. Its key correctness property is conditional unbiasedness: the expected empirical measure after resampling equals the weighted empirical measure before resampling. Resampling does not create new information or guarantee convergence; it trades unequal weights for sampling noise and duplicated particles.

## Learning objectives

By the end of the chapter, you should be able to:

- define a weighted empirical measure for a finite particle population;
- construct multinomial ancestor indices from normalized weights;
- prove resampling is conditionally unbiased for test functions;
- compute resampling variance and duplicate probabilities in small examples;
- explain the tradeoff between weight concentration and genealogical collapse;
- encode a finite particle system using PMFs, kernels, and conditional expectation.

## 1. A weighted particle population

Let the particle states be `x₁,…,x_N` in a finite state type `E`, with nonnegative weights `w₁,…,w_N`. Assume the total weight

\[
  W=\sum_{i=1}^Nw_i
\]

is positive. The normalized weights are `α_i=w_i/W`, and the weighted empirical measure is

\[
  \eta^N=\sum_{i=1}^N\alpha_i\delta_{x_i}.
\]

For an observable `φ`, its particle estimate is

\[
  \eta^N(φ)=\sum_{i=1}^N\alpha_iφ(x_i).
\]

Particles may share the same state. The indexed population and the induced measure are different objects: two indices can represent two copies of the same state, and their weights still contribute separately. Keep the index type `Fin N` in the particle representation even if the state type has duplicates.

If `W=0`, normalized weights are undefined. In an importance sampler this means every particle has zero target weight, so no weighted empirical distribution exists. A totalized program can return a fallback population, but correctness theorems should assume `W>0` or explicitly analyze the fallback branch.

## 2. Multinomial resampling

Draw ancestor indices `A₁,…,A_N` independently with

\[
  \mathbb{P}(A_j=i)=\alpha_i.
\]

The resampled particles are `x_{A₁},…,x_{A_N}` and receive equal weights `1/N`. Their empirical measure is

\[
  \widehat\eta^N=\frac1N\sum_{j=1}^N\delta_{x_{A_j}}.
\]

The resampling randomization is completely specified by the product PMF on `Fin N → Fin N`. In a finite formalization, define the one-index categorical PMF from `α`, then use the product construction to obtain independent indices. The ancestor map turns that random index vector into the output particle vector.

The map has two layers: sample indices according to normalized weights, then map indices to stored states. Separating these makes it possible to prove properties of the resampler without unfolding the state space or the transition model that generated the particles.

This decomposition also isolates measurable structure. The index-to-state map is deterministic, while the only random choice is the ancestor vector. Its pushforward law can be reused for several observables without rebuilding the categorical calculation each time.

## 3. Conditional unbiasedness

Condition on the current particle states and weights. For each test function `φ`,

\[
\begin{aligned}
  \mathbb{E}[\widehat\eta^N(φ)\mid x_{1:N},w_{1:N}]
  &=\frac1N\sum_{j=1}^N\mathbb{E}[φ(x_{A_j})\mid x_{1:N},w_{1:N}]\\
  &=\frac1N\sum_{j=1}^N\sum_{i=1}^N\alpha_iφ(x_i)\\
  &=\eta^N(φ).
\end{aligned}
\]

Thus the resampled empirical measure is unbiased conditionally on the weighted population. For a finite state space, equality of integrals for all indicator functions implies equality of the expected measure and the original weighted empirical measure.

This statement does not say the realized empirical measures are equal. Resampling is random and usually changes the population. It says that averaging over the resampling randomness recovers the weighted estimate. In Lean, formulate the theorem first for a real-valued `φ`; then specialize to indicators or point masses if measure equality is needed.

For a finite state space, take `φ` to be the indicator of each singleton. The expected mass assigned to each state then equals its weighted empirical mass, and extensionality of finite measures gives equality of the expected measure and `η^N`. On an infinite state space, test-function equality needs an appropriate measure-determining class and integrability conditions; the finite point-mass argument should not be generalized without those hypotheses.

## 4. Worked example: two particles with unequal weights

Take two distinct states `a` and `b` with weights `3/4` and `1/4`, and resample `N=2` indices independently. Let `K` be the number of copies of `a` after resampling. Then `K` is binomial with parameters `2` and `3/4`:

\[
  \mathbb{P}(K=2)=\frac9{16},\qquad
  \mathbb{P}(K=1)=\frac6{16},\qquad
  \mathbb{P}(K=0)=\frac1{16}.
\]

The resampled fraction of `a` is `K/2`. Its expected value is `3/4`, matching the weighted empirical mass, and its variance is

\[
  \operatorname{Var}(K/2)
  =\frac{(3/4)(1/4)}{2}=\frac3{32}.
\]

The output is duplicated with probability `9/16+1/16=10/16`, even though the input contained two distinct states. Resampling is unbiased but can immediately reduce the number of distinct states.

This example is a useful exact Lean exercise. Represent the ancestor vector as the four elements of `Fin 2 → Fin 2`, compute its product probability, and sum over the three possible counts. The general proof uses indicator variables and independence; the enumeration checks that the indexing and normalization conventions agree.

## 5. Conditional variance of a resampled estimate

For a fixed observable `φ`, each resampled value `φ(x_{A_j})` is an independent draw from the discrete distribution on particle values induced by `α`. Therefore

\[
  \operatorname{Var}(\widehat\eta^N(φ)\mid x_{1:N},w_{1:N})
  =\frac1N\left(\sum_i\alpha_iφ(x_i)^2
        -\left(\sum_i\alpha_iφ(x_i)\right)^2\right).
\]

The variance shrinks like `1/N` for a fixed weighted population and bounded observable. It is zero when all particles have the same observable value, even if their states differ. The expression is the variance under the weighted empirical distribution divided by the number of resampled particles.

The conditional form matters in a sequential algorithm. The current particles are themselves random, so the unconditional variance combines the variation in the current weighted estimate with the additional resampling variance. The law of total variance separates these two contributions. Proving only the conditional formula does not establish the total error of a particle filter, but it gives one of its components.

The offspring count of particle `i` is `N_i=|{j : A_j=i}|`. It has mean `Nα_i` and variance `Nα_i(1-α_i)`. For distinct `i` and `k`, the counts have covariance `-Nα_iα_k`, because their sum is fixed at `N`. These formulas explain why a high-weight ancestor is copied repeatedly while low-weight ancestors can vanish. They also give reusable finite lemmas for analyzing genealogy without reasoning about the particle states themselves.

If `\mathcal F` contains the current weighted population, the law of total variance gives

\[
  \operatorname{Var}(\widehat\eta^N(φ))
  =\mathbb{E}[\operatorname{Var}(\widehat\eta^N(φ)\mid\mathcal F)]
   +\operatorname{Var}(\eta^N(φ)).
\]

The first term is resampling noise; the second is the error already present in the weighted particle approximation. The tower property similarly lifts conditional unbiasedness to unconditional unbiasedness for the one-step resampled estimate. This decomposition is a bridge from the local resampler theorem to a sequential martingale analysis.

## 6. Resampling trades weight degeneracy for duplicates

Before resampling, a few particles may carry almost all the total weight. After resampling, all particles have equal weights, but high-weight ancestors appear repeatedly and low-weight ancestors can disappear. This reduces the variation in the weights while increasing dependence among the particle states.

The effective sample size

\[
  \operatorname{ESS}=\frac{(\sum_iw_i)^2}{\sum_iw_i^2}
\]

is often used as a trigger for resampling. Equal weights give ESS `N`; if one weight dominates, ESS approaches one. The threshold is an algorithmic design choice, not a correctness theorem. ESS does not count distinct states and can be high even when all particles occupy the same state.

Resampling every time step may cause rapid genealogical collapse: many current particles share a small number of ancestors. Delaying resampling can preserve diversity but leaves highly unequal weights. Adaptive schedules balance these effects. A formal proof of the filtering target should be independent of the chosen schedule whenever each resampling operation preserves the relevant conditional expectation.

The expected number of distinct selected ancestors is

\[
  \sum_{i=1}^N\left(1-(1-\alpha_i)^N\right),
\]

since particle `i` is absent exactly when all `N` draws choose something else. This statistic is different from ESS: ESS depends on the weight squares, while the expected number of ancestors depends on the sample count and the probabilities of zero offspring.

Residual, stratified, and systematic resampling use different dependence structures among the ancestor choices. Many such schemes are designed to retain the same conditional expectation while reducing variance for selected classes of test functions. A proof should establish unbiasedness and any variance comparison for the particular scheme; multinomial calculations do not transfer automatically.

Multinomial resampling is the easiest specification because every index is an independent categorical draw. Residual resampling first assigns deterministic integer offspring counts and randomizes only the remaining fractional mass. Stratified resampling allocates one draw to each probability interval, while systematic resampling uses a single random offset across evenly spaced points. These alternatives introduce dependence among offspring counts; their proof states should expose that dependence rather than reuse an independence theorem.

## 7. Worked example: resampling with repeated states

Suppose the particle list is `(a,a,b)` with weights `(1/4,1/4,1/2)`. The weighted empirical mass of `a` is `1/2`, not `1/4`, because two particle indices map to `a`. A resampling index chooses each of the three slots with probabilities `(1/4,1/4,1/2)`, so the probability that the selected state is `a` is `1/2`.

This example distinguishes the index distribution from the state distribution. If the proof first deduplicates states, it must combine their weights. Keeping indices avoids that extra aggregation and is usually the better representation for implementation proofs. Conversely, a theorem about measures on `E` should sum all indices that map to the same state.

In Lean, define the state projection `x : Fin N → E` and push the categorical distribution on indices forward through `x`. The pushforward expectation formula gives the state-level resampling law. This is a direct use of measure mapping and avoids an unnecessary quotient by duplicate particle values.

## 8. Resampling as a conditional kernel

When the weighted population itself is random and measurable, the resampling distribution depends on that population. Mathematically, this is a conditional kernel from the current particle configuration to the next particle configuration. Its conditional expectation identity is the reusable correctness theorem.

The filtration records the information available before resampling. Conditional on that information, the ancestor draws are independent with probabilities determined by the current weights. After resampling, the next particle population is measurable with respect to the enlarged filtration. This places particle methods in the same adapted-process framework as Chapters 35–39.

For finite state and finite particle count, all configuration spaces are finite, so one can define the kernel by explicit probabilities. For larger or general measurable spaces, use kernel composition and conditional expectation rather than manually enumerating outputs. The proof structure is unchanged: show the conditional law, integrate a test function, and simplify to the weighted empirical expectation.

With a finite configuration space, `PMF.integral_eq_sum` converts the conditional expectation into a sum over ancestor vectors. Independence factors each vector probability into a product of normalized weights. Reordering the finite sum makes each output position contribute the same weighted average; averaging over `N` positions leaves that average unchanged. This proof is a good place to use a helper lemma for one resampled coordinate and then sum over output coordinates.

## 9. Sequential particle filtering

A bootstrap particle filter alternates three steps:

1. propagate each particle through the state-transition kernel;
2. multiply each propagated particle's weight by its observation likelihood;
3. resample if the chosen schedule requires it.

The proposal may differ from the state-transition kernel; then each weight includes the transition likelihood ratio from Chapter 53. If the algorithm resamples, the selected particles begin the next stage with equal weights. The exact filter recursion is approximated by a random empirical measure, and conditional unbiasedness explains why a single resampling step does not shift its expectation.

This local unbiasedness is not by itself a complete finite-`N` error theorem. The particles at later times are dependent, weights are random, and resampling decisions may be adaptive. Error bounds require a separate analysis of the transition and potential sequence, often using martingale decompositions or stability estimates. Chapter 52's iid variance formula cannot be applied directly to a particle population after resampling.

When resampling is skipped, the algorithm must carry forward the product of previous weights; when resampling occurs, the selected particles are commonly assigned equal weights and begin a new accumulation period. A precise algorithm definition should include this weight-reset rule and whether the normalizing-constant estimate includes the average weight at every stage. Those choices do not change the local resampling identity, but they do change the estimator being analyzed.

## 10. A proof workflow

1. Represent the particle population by an indexed vector of states and nonnegative weights.
2. Prove the total weight is positive before normalization.
3. Define the categorical PMF on ancestor indices.
4. Construct independent ancestor draws as a finite product distribution.
5. Map the sampled indices to particle states.
6. Prove the conditional expectation identity for a generic observable.
7. Derive the conditional variance from independence.
8. Keep resampling randomness separate from propagation randomness.
9. Use conditional expectation or a filtration for repeated time steps.
10. State a separate theorem for global particle-filter error or normalizer estimates.

## 11. Common failure modes

### Weights are normalized when their sum is zero

Assume positive total weight or define and analyze a fallback branch.

### Particle indices are confused with particle states

Different indices may represent identical states; their weights still add.

### Conditional unbiasedness is called pathwise equality

The resampled population is random. Only its conditional expectation equals the weighted empirical measure.

### Equal weights are said to remove dependence

Resampled particles share ancestors and are generally dependent.

### ESS is treated as the number of distinct particles

ESS measures weight concentration, not state diversity.

### The iid sample-mean theorem is reused after resampling

Conditional independence holds for draws at one resampling step, not for the entire particle history.

### A local resampling identity is presented as a global accuracy theorem

Sequential error needs additional control of the propagated and weighted particle system.

## 12. Exercises

1. Define the weighted empirical measure from particle states and weights.
2. Construct multinomial ancestor indices from normalized weights.
3. Prove conditional unbiasedness for a bounded observable.
4. Compute the two-particle duplication probabilities in Section 4.
5. Derive the conditional variance of a resampled empirical average.
6. Explain why repeated states require summing weights over their indices.
7. Compare ESS with the number of distinct particle states.
8. Describe how a resampling step is represented as a conditional kernel.
9. List the steps of a bootstrap particle filter.
10. Explain why conditional unbiasedness does not imply a complete finite-particle error bound.
11. Identify which independence assumptions hold at one resampling step.
12. Connect the particle filtration to the martingale chapters earlier in the book.

## Summary

Multinomial resampling draws ancestor indices according to normalized particle weights and assigns equal weights to the resulting population. Its empirical measure is conditionally unbiased, and its conditional variance is the weighted empirical variance divided by the particle count. Resampling reduces weight inequality but creates duplicates and dependence. A full particle filter composes propagation, likelihood weighting, and optional resampling; global error requires more than the local resampling identity.

## Further reading

- [Mathlib: Probability mass functions and integrals](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Integrals.html)
- [Mathlib: Kernel composition](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html)
- Chapters 35–39 for conditional expectation, filtrations, and martingales.
- Chapters 51–53 for importance sampling, variance, and sequential filtering.
