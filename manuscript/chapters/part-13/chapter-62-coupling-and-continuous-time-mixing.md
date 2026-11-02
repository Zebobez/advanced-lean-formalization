# Chapter 62 — Coupling and Continuous-Time Mixing

> **Audience.** This chapter assumes familiarity with finite-state transition kernels, total variation, Markov chains, and continuous-time generators. It develops coupling constructions that turn a joint process into quantitative convergence bounds.

Coupling studies two random variables or processes on one probability space while preserving their individual laws. The joint dependence is chosen to make them agree quickly. Once two copies of the same Markov chain meet and remain together, the probability that they have not met by time t bounds the distance between their marginal laws.

In continuous time, a coupling can be built at the generator level or through uniformization. The generator view records joint jump rates directly. The uniformized view places both chains on a common Poisson clock and couples their discrete updates. The latter is particularly natural after Chapter 56; both approaches expose a finite-state proof that can be separated from the general measure-theoretic definition of total variation.

## Learning objectives

By the end of the chapter, you should be able to:

- define a coupling of two finite probability laws;
- prove the coupling inequality for total variation;
- construct a coalescent coupling of two copies of a finite-state chain;
- use a coupling-time tail to bound continuous-time mixing;
- build a joint transition rule by maximal coupling after uniformization;
- formulate generator couplings and path-coupling drift conditions in Lean.

## 1. Couplings of probability laws

Let μ and ν be probability distributions on a finite state set S. A coupling is a joint distribution Γ on S×S whose first marginal is μ and whose second marginal is ν. If (X,Y) has law Γ, then X has law μ and Y has law ν, but their dependence is chosen by the constructor.

The total variation distance in the common probability convention is
\[
  d_{\mathrm{TV}}(\mu,\nu)
    =\frac12\sum_{x\in S}|\mu(x)-\nu(x)|.
\]
For every coupling,
\[
  d_{\mathrm{TV}}(\mu,\nu)\leq\Pr(X\ne Y).
\]
To see this, fix a subset A⊆S. The indicators of X∈A and Y∈A agree whenever X=Y, so
\[
  |\Pr(X\in A)-\Pr(Y\in A)|\leq\Pr(X\ne Y).
\]
Taking the supremum over A gives the usual event form of total variation and hence the inequality.

On a finite state space, an optimal coupling exists. Its probability of agreement is
\[
  \sum_x\min(\mu(x),\nu(x)),
\]
so its mismatch probability equals dTV(μ,ν). This is called a maximal coupling. For a proof, place the common mass min(μ(x),ν(x)) on each diagonal pair (x,x), then couple the residual masses. At each state at least one residual is zero, so the residual supports are disjoint and cannot create additional agreements.

The coupling inequality does not require maximality. Any explicit joint construction gives a valid upper bound, and a mathematically convenient coupling may be easier to formalize than an optimal one.

The same argument applies to arbitrary initial laws. Begin the pair process
with any coupling Γ of μ and ν, then evolve it with a joint transition rule
whose marginals are the desired chains. At time t, the coordinate laws are
μP_t and νP_t, so
\[
  d_{\mathrm{TV}}(\mu P_t,\nu P_t)
    \leq\Pr_\Gamma(X_t\ne Y_t).
\]
This separates the choice of initial coupling from the choice of joint
dynamics. A maximal initial coupling can reduce the initial mismatch, while
a coalescent transition rule controls later disagreement.

The maximal construction can be written as a formula. Let
\(c(x)=\min(\mu(x),\nu(x))\), let \(\alpha=\sum_xc(x)\), and define residual
masses \(\mu'(x)=\mu(x)-c(x)\) and \(\nu'(x)=\nu(x)-c(x)\). If \(\alpha<1\),
put common mass \(c(x)\) on each diagonal pair and add the residual product
\[
  \Gamma(x,y)
    =\mathbf 1_{\{x=y\}}c(x)
      +\frac{\mu'(x)\nu'(y)}{1-\alpha}.
\]
If \(\alpha=1\), use only the diagonal mass. The residual distributions
have disjoint supports: at each state, at least one of \(\mu'(x)\) and
\(\nu'(x)\) is zero. Thus the residual product creates no extra agreement,
and the mismatch probability is exactly \(1-\alpha=d_{\mathrm{TV}}(\mu,\nu)\).
This formula is finite algebra and gives a direct formal construction.

## 2. Total-variation normalization

Mathlib’s measure-theoretic distance tvDist uses the unnormalized total variation convention: for probability measures it is twice the common dTV defined above. This is the convention developed in Chapter 48. Therefore the coupling inequality becomes
\[
  \mathsf{tvDist}(\mu,\nu)\leq2\Pr(X\ne Y).
\]
Keeping both versions visible avoids a common factor-of-two error. If a theorem uses Mathlib’s tvDist, either use this inequality or state every bound in the normalized convention and convert once at the interface.

On a finite state type, the atom formula makes the conversion explicit:
\[
  \mathsf{tvDist}(\mu,\nu)
    =\sum_x|\mu(x)-\nu(x)|
    =2d_{\mathrm{TV}}(\mu,\nu).
\]
The general measure definition is useful for non-discrete spaces; the finite sum is usually the more convenient form for a finite-chain coupling proof.

## 3. Coupling two continuous-time chains

Let Q be a generator on S. A coupling generator is a generator \(\bar Q\) on S×S such that each coordinate evolves according to Q. Writing \(\pi_1(x,y)=x\) and \(\pi_2(x,y)=y\), the marginal requirement is
\[
  \bar Q(f\circ\pi_1)(x,y)=Qf(x),\qquad
  \bar Q(f\circ\pi_2)(x,y)=Qf(y)
\]
for every function f:S→ℝ.

Start the coupled chain at (x,y), and call its coordinates X_t and Y_t. Each coordinate has the correct transition law, so their marginals are P_t(x,·) and P_t(y,·). A coalescent coupling has the additional property that once X_t=Y_t, the pair stays on the diagonal. Define the coupling time
\[
  \tau=\inf\{t\geq0:X_t=Y_t\}.
\]
Then {τ>t} is exactly the event that the coordinates are still different at time t, and
\[
  d_{\mathrm{TV}}\bigl(P_t(x,\cdot),P_t(y,\cdot)\bigr)
    \leq\Pr_{x,y}(\tau>t).
\]
In Mathlib’s tvDist convention, the right side is multiplied by two.

For an arbitrary coupling that can split after meeting, the general inequality with \(\Pr(X_t\ne Y_t)\) remains true, but the first meeting time no longer controls that probability. The diagonal must be made invariant if the coupling time is to provide the stated tail bound.

## 4. Coupling through a common Poisson clock

Choose a uniformization rate Λ and form the stochastic matrix R=I+Q/Λ. On the pair state space S×S, use one rate-Λ Poisson clock. At a candidate event, when the current pair is (x,y), sample a joint transition law Γ_{x,y} on S×S whose marginals are R(x,·) and R(y,·). The two coordinates then have the correct uniformized transition matrix.

If x=y, choose the diagonal coupling of the identical row R(x,·) with itself: draw one next state z and move to (z,z). Thus the diagonal is absorbing for the pair process. If x≠y, a maximal coupling of the two rows maximizes the chance of meeting at the next event.

The continuous-time coupled process inherits the desired marginals because the same clock rate and each coordinate’s one-step marginal agree with the original uniformization. Candidate self-transitions remain harmless: an event can leave one coordinate fixed, both fixed, or move both, but the marginal law of each coordinate is still R.

This construction gives a practical Lean decomposition:

1. Prove each Γ_{x,y} is a probability law with the two required marginals.
2. Package these laws as a Markov kernel on S×S.
3. Prove the diagonal transition rule preserves equality.
4. Compose the joint kernel at Poisson event times.
5. Transfer the resulting coupling-time estimate to marginal total variation.

The general kernel composition interface is useful for composing the joint transitions. The maximal-coupling formula itself is a finite-state construction; do not assume the kernel composition API automatically supplies a maximal coupling theorem.

If there is a uniform lower bound δ>0 on the chance that a coupled event
makes the two states equal whenever they are different, then the probability
of surviving n candidate events without coalescing is at most
\((1-\delta)^n\). Averaging over the Poisson count gives
\[
  \Pr(\tau>t)
   \leq e^{-\Lambda t}
       \sum_{n=0}^{\infty}\frac{(\Lambda t)^n}{n!}(1-\delta)^n
   =e^{-\Lambda\delta t}.
\]
The first inequality conditions on the number of events and uses the
per-event success bound; the equality is the exponential series. Thus a
finite-state one-step estimate can become an explicit continuous-time
mixing rate without solving a matrix differential equation.

## 5. From a coupling-time tail to mixing

Suppose a coalescent coupling can be constructed for every pair x,y and satisfies a uniform tail estimate
\[
  \sup_{x,y}\Pr_{x,y}(\tau>t)\leq C e^{-\rho t}
\]
for constants C≥0 and ρ>0. Then
\[
  \sup_{x,y}
  d_{\mathrm{TV}}\bigl(P_t(x,\cdot),P_t(y,\cdot)\bigr)
  \leq C e^{-\rho t}.
\]
If π is stationary, average the second initial state against π:
\[
  d_{\mathrm{TV}}\bigl(P_t(x,\cdot),\pi\bigr)
  \leq C e^{-\rho t}.
\]
This yields a mixing-time bound by solving \(Ce^{-\rho t}\leq\varepsilon\).

The coupling estimate can be stronger than a spectral-gap estimate when the coupling time has a sharp tail, or weaker when the chosen joint dynamics meet slowly. It is a proof method, not a uniquely defined constant. Different couplings of the same pair of chains can lead to very different meeting times.

If the tail bound depends on the initial pair, retain that dependence:
\[
  d_{\mathrm{TV}}(P_t(x,\cdot),P_t(y,\cdot))
    \leq \Pr_{x,y}(\tau>t).
\]
Only after proving a uniform estimate should the supremum over x,y be
taken. This order can preserve sharper bounds for nearby starting states.

## 6. Worked example: the two-state chain

Consider the chain with rate a>0 from 0 to 1 and b>0 from 1 to 0. Use uniformization with Λ=a+b. As shown in Chapter 56, both rows of R are the stationary law \((b/(a+b),a/(a+b))\).

Start two copies at 0 and 1. At the first Poisson event, use the diagonal coupling of the identical rows: sample one state from the stationary row and set both coordinates to that state. They then remain equal. Thus τ is exactly the first event time of the rate-(a+b) Poisson clock, so
\[
  \Pr(\tau>t)=e^{-(a+b)t}.
\]
The standard total-variation distance between the two transition laws is also \(e^{-(a+b)t}\), so the coupling bound is sharp. In Mathlib’s unnormalized convention, tvDist is \(2e^{-(a+b)t}\), which matches the factor-two version of the coupling inequality.

This example shows that a coupling can explain an exact convergence rate. It also shows why a shared event clock matters: if each coordinate used an independent Poisson clock, there would be no automatic simultaneous update that sends both states to the common row in one event.

## 7. Worked example: complete-graph coalescence

On n states, let every off-diagonal rate be r>0. Choose Λ=nr, which is at least the exit rate (n−1)r. Then
\[
  R(x,y)=\frac1n
\]
for every pair x,y, including the diagonal. Every candidate event replaces the current state by a fresh uniform state.

For two copies at any pair of states, couple the next uniform draws identically. The pair coalesces at the first clock event, whose waiting time is exponential with rate nr. Hence
\[
  \sup_{x,y}d_{\mathrm{TV}}\bigl(P_t(x,\cdot),P_t(y,\cdot)\bigr)
  \leq e^{-nrt}.
\]
The spectral-gap calculation in Chapter 60 gives the same decay rate nr. Here the coupling and eigenvalue methods agree exactly.

The matrix R has identical rows, so after one event the coordinates agree with probability one under the chosen coupling. For other chains, the rows differ and maximal coupling may only produce agreement with some probability at each event. A one-step lower bound on this agreement probability can still yield a geometric tail in the number of clock events and, after averaging the Poisson count, an exponential tail in time.

## 8. Path coupling and metric contraction

Sometimes it is easier to couple only neighboring states in a graph or metric, then extend the estimate to arbitrary pairs by chaining paths. Let d be a metric on S. Suppose a coupling generator \(\bar Q\) satisfies
\[
  (\bar Q d)(x,y)\leq-\rho\,d(x,y)
\]
for x≠y, with the diagonal absorbing. Here d is viewed as a function on S×S. Differentiating the expected distance along the coupled process gives
\[
  \frac{d}{dt}\mathbb E_{x,y}[d(X_t,Y_t)]
  \leq-\rho\,\mathbb E_{x,y}[d(X_t,Y_t)].
\]
Therefore the expected distance decays at least as \(e^{-\rho t}d(x,y)\).

Let d_min be the smallest positive distance between distinct states. Then
\[
  \mathbf 1_{\{X_t\ne Y_t\}}
    \leq\frac{d(X_t,Y_t)}{d_{\min}},
\]
so the coupling inequality yields
\[
  d_{\mathrm{TV}}\bigl(P_t(x,\cdot),P_t(y,\cdot)\bigr)
  \leq \frac{d(x,y)}{d_{\min}}e^{-\rho t}.
\]
This is a continuous-time path-coupling bound. A local drift calculation for adjacent pairs can establish a global mixing estimate when the metric and graph structure support the path extension.

The method is distinct from requiring that the two chains meet immediately. It controls expected distance first, then converts distance to mismatch. For a metric with many scales, that can be more natural than designing a maximal coupling at every pair of states.

## 9. Lean formalization strategy

For finite S, represent a coupling law by a probability distribution on S×S and prove its marginals using finite sums. For a process coupling, use either a joint generator on S×S or a joint transition matrix at uniformization events. The generator approach makes drift inequalities direct; the event-kernel approach makes the construction from maximal row couplings explicit.

State the total-variation convention at the boundary of the theorem. Mathlib’s tvDist is twice the standard probability convention, while the elementary coupling inequality is most often remembered with the half-normalized distance. A helper lemma translating the finite atom sum to tvDist prevents that normalization choice from appearing throughout the proof.

Mathlib provides total variation distance for finite measures and Markov-kernel composition. These are useful building blocks. A CTMC-specific coalescent coupling, a coupling-time theorem, or a path-coupling drift estimate still needs to be constructed from the joint transition data. Keep marginal correctness, diagonal invariance, and the tail estimate as separate lemmas.

For the common-clock construction, use Chapter 56’s uniformization rate and matrix. Prove the row marginals of the coupled event kernel before discussing continuous time. The clock then acts on both coordinates at once, and the Poisson event count converts a discrete per-event estimate into a time-dependent bound.

## 10. Common failure modes

### Only the marginal chains are checked informally

A coupling must prove both marginal laws exactly; a plausible joint transition table may alter one coordinate’s rates.

### The pair is allowed to separate after meeting

Then the first meeting time does not bound the mismatch event at later times.

### Candidate events are treated as actual jumps

Uniformization includes self-transitions. Define the joint event kernel and state-change events separately.

### The total-variation factor is omitted

Mathlib’s tvDist is unnormalized. The standard coupling inequality uses the half-normalized convention.

### A good coupling is assumed to be maximal

Maximal coupling is optimal for one-step agreement, but a non-maximal coupling may have a better long-run coalescence structure.

## 11. Exercises

1. Prove the coupling inequality using the event characterization of total variation.
2. Construct a maximal coupling of two probability vectors using their pointwise minimum.
3. Show that the residual supports in the maximal-coupling construction are disjoint.
4. State the generator marginal conditions for a coupling on S×S.
5. Prove that a diagonal-preserving joint generator yields a coalescent coupling.
6. Derive the continuous-time coupling bound from the coupled marginals.
7. Work out the shared-clock coupling for the two-state chain and compare with its exact transition distance.
8. For the complete graph, compute the exit rate, uniformization rate, and coupling-time distribution.
9. Prove the path-coupling estimate from a generator drift inequality for d.
10. Convert the standard dTV coupling estimate into Mathlib’s tvDist convention.

## Summary

A coupling places two chains on one probability space while preserving each marginal law. The probability that their states differ bounds the standard total-variation distance; Mathlib’s tvDist convention is twice that distance. A coalescent coupling makes the diagonal absorbing, so a tail bound on the coupling time becomes a mixing bound. Uniformization supplies a common Poisson clock, and generator couplings or path-coupling drift inequalities provide additional ways to design and analyze the joint dynamics.

## Further reading

- [Mathlib: Total variation distance for finite measures](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/TotalVariation/Defs.html)
- [Mathlib: Properties of total variation distance](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/TotalVariation/Basic.html)
- [Mathlib: Markov kernel composition](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html)
- Chapter 48 for total-variation contraction and discrete-time coupling.
- Chapters 56 and 60 for uniformization and spectral-gap mixing bounds.
