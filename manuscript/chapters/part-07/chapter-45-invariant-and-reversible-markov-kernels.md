# Chapter 45 — Invariant and Reversible Markov Kernels

> **Audience.** This chapter assumes familiarity with Markov kernels, kernel composition, probability measures, and irreducibility. It develops invariant measures and detailed balance as properties of transition kernels.

A probability distribution is stationary for a Markov chain when one transition leaves it unchanged. The measure-theoretic formulation replaces a transition matrix with a kernel and a row vector with a measure: binding the measure with the kernel must return the same measure. Reversibility is a stronger symmetry condition that compares probability flow in both directions between measurable sets.

These properties are central in Markov-chain arguments and in the analysis of Monte Carlo algorithms. Mathlib provides a small, compositional interface: `Kernel.Invariant` expresses stationarity, `Kernel.IsReversible` expresses detailed balance, and a reversible Markov kernel is invariant. The proof strategy is to work at the measure level first, then specialize to finite-state equations when appropriate.

The distinction between invariance and reversibility matters. Every reversible kernel is invariant, but an invariant distribution need not satisfy detailed balance. A chain can circulate probability around a cycle while preserving its uniform distribution, even though the flow is not symmetric edge by edge.

## Learning objectives

By the end of the chapter, you should be able to:

- state invariance as `μ.bind κ = μ`;
- formulate detailed balance for measurable sets;
- prove invariance from reversibility for a Markov kernel;
- reduce finite-state invariance and reversibility to matrix equations;
- show that composing kernels preserving a measure preserves it;
- distinguish stationary distributions from reversible dynamics.

## 1. Invariance of a measure

Let `κ : Kernel α α` be a transition kernel on one state space. Applying the kernel to a measure `μ` produces the next-step law `μ.bind κ`, written `κ ∘ₘ μ`. The measure is invariant if

\[
  \kappa.\mathrm{Invariant}(\mu)
  \quad\Longleftrightarrow\quad
  \mu\mathbin{\mathrm{bind}}\kappa=\mu.
\]

For a Markov kernel and a probability measure, this says that if the current state has law `μ`, then the next state has the same law. It does not say the state itself remains unchanged on each path. A stationary chain may move at every step while its marginal distribution is constant.

The measure equality is a good API boundary. To prove it, one may compare values on measurable sets or use integral characterizations. Once established, downstream results use `Kernel.Invariant` without knowing how the measure was represented.

There are two useful ways to read this definition. Operationally, start with a random state of law `μ`, sample one transition using `κ`, and inspect the output law. The kernel is invariant when the output law is again `μ`. Algebraically, `bind` is an action of kernels on measures, and invariance says that `μ` is a fixed point of that action. The operational view guides examples; the algebraic view guides reusable proofs.

In Lean, keep the direction of `bind` visible while developing the proof. If the goal is stated using `μ.bind ⇑κ`, rewrite toward that expression rather than repeatedly unfolding the kernel into its values. A proof that establishes an equality of measures can then be reused for every measurable set and every integrable observable. Unfolding too early usually creates nested integrals before the proof has identified the right invariant structure.

```text
current law μ ── transition kernel κ ──▶ next law κ ∘ₘ μ
      ▲                                        │
      └──────────── invariant: same μ ─────────┘
```

In finite spaces, write `μ` as a row vector and `κ` as a row-stochastic matrix `P`. Invariance becomes `πP=π`. This is a finite family of linear equations together with nonnegativity and total mass one. In general measurable spaces, kernel binding and measure equality are the corresponding abstract formulation.

## 2. Reversibility and detailed balance

A kernel `κ` is reversible with respect to `π` when the mass flowing from any measurable set `A` to any measurable set `B` equals the mass flowing in the reverse direction:

\[
  \int_A \kappa(x)(B)\,d\pi(x)
  =\int_B \kappa(x)(A)\,d\pi(x).
\]

Mathlib names this predicate `Kernel.IsReversible κ π`. In a finite or countable discrete space, it reduces on singleton sets to detailed balance:

\[
  \pi(x)\,\kappa(x,\{y\})
  =\pi(y)\,\kappa(y,\{x\}).
\]

Detailed balance is a symmetry of stationary probability flow, not necessarily a symmetry of the transition probabilities themselves. If `π(x)` and `π(y)` differ, the transition rates from `x` to `y` and from `y` to `x` may differ while the weighted flows remain equal.

The set formulation is deliberately stronger in appearance than a matrix identity: it works on arbitrary measurable spaces without assuming atoms, a countable state type, or a density with respect to a reference measure. In a discrete space, testing on singleton sets extracts the familiar pointwise equations. In a continuous space, detailed balance can instead be expressed as symmetry of the joint measure on pairs `(x,y)` obtained by first sampling `x` from `π` and then sampling `y` from `κ x`.

That joint-measure perspective explains why the predicate quantifies over two sets. The mass assigned to `A × B` must agree with the mass assigned to `B × A` after swapping coordinates. It also suggests a proof strategy: identify the two-step joint distribution, show it is invariant under the coordinate swap, then derive the set-integral equality. For kernels with densities, the pointwise condition

\[
  \pi(dx)\,k(x,y)\,\lambda(dy)
  =\pi(dy)\,k(y,x)\,\lambda(dx)
\]

is one way to establish that symmetry, provided all density and integrability assumptions are justified.

Mathlib proves `Kernel.IsReversible.invariant`: if `κ` is Markov and reversible with respect to `π`, then `π` is invariant. The Markov hypothesis supplies total mass one for each transition row; reversibility alone for a subprobability kernel does not imply preservation of the total measure.

## 3. Worked example: a two-state reversible chain

Consider the transition matrix

\[
  P=\begin{pmatrix}1-p&p\\q&1-q\end{pmatrix},
  \qquad 0<p,q<1.
\]

The stationary distribution is

\[
  \pi_0=\frac{q}{p+q},\qquad
  \pi_1=\frac{p}{p+q}.
\]

There are two off-diagonal detailed-balance equations, but they are the same calculation:

\[
  \pi_0 P_{01}=\frac{q}{p+q}p
  =\frac{p}{p+q}q=\pi_1P_{10}.
\]

The diagonal equations hold identically. Thus `P` is reversible with respect to `π`, and the library theorem yields invariance. One can also verify `πP=π` directly; the reversible proof is more informative because it explains the symmetry of the transition flow.

In Lean, use a finite state type such as `Fin 2` with a discrete measurable structure. Define the kernel rows from the two probability measures and define `π` by its two atom masses. Establish the scalar detailed-balance identities, then prove `IsReversible` by reducing measurable subsets to unions of singleton atoms. The general invariance theorem avoids a second independent calculation of `π.bind κ`.

The formalization becomes easier if the numerical argument is separated from the measure argument. First prove that the candidate weights sum to one and are nonnegative. Next prove the two off-diagonal flow equations. Only then use a finite-sum lemma to lift the atomwise identities to arbitrary sets. In a two-point type, the lift is a short case split; for a larger finite type, it is usually cleaner to state a finite-sum identity and use `Finset.sum_congr` than to enumerate every subset.

Boundary cases are informative. If `p=0` or `q=0`, the displayed formula needs separate care: the chain has absorbing states and stationary measures need not be unique. The strict assumptions `0<p,q<1` ensure both transitions occur and the candidate assigns positive mass to both states. A library proof should either carry those hypotheses explicitly or handle degenerate cases in separate branches rather than asking a denominator simplifier to solve the mathematical issue.

## 4. Worked example: a reversible random walk on a graph

Let a finite undirected graph have positive degree at every vertex. Define a random walk that chooses a neighboring vertex uniformly. For an edge `{x,y}`, the transition probability is `1/deg(x)` from `x` to `y`. Set

\[
  \pi(x)=\frac{\deg(x)}{\sum_z\deg(z)}.
\]

Then

\[
  \pi(x)P(x,y)=\frac{1}{\sum_z\deg(z)}
  =\pi(y)P(y,x)
\]

whenever `x` and `y` are adjacent. If they are not adjacent, both sides are zero. The degree-weighted distribution is therefore reversible and hence stationary.

This example illustrates why a uniform measure is not always stationary. Vertices with high degree are visited more often by the simple random walk, so their stationary weights are larger. In formalization, prove the edgewise identity once and extend it to measurable sets by finite summation.

If the graph is regular, all degrees agree and the stationary measure is uniform. Thus the regular-graph case is a useful simplification after the general degree-weighted proof has been established.

## 5. Invariant measures are stable under composition

If two kernels `κ` and `η` both preserve `μ`, then their composition preserves `μ` as well. Indeed, applying first one kernel and then the other leaves the measure unchanged at each stage. Mathlib packages this as `Kernel.Invariant.comp`.

This is useful for multi-step transitions. If `κ` preserves `μ`, then every kernel power `κ^n` preserves it, by induction and the composition theorem. The stationary distribution of a one-step Markov chain is therefore stationary at every deterministic horizon.

The result also supports splitting a transition into stages. If a simulation algorithm alternates two update kernels that each preserve the same target distribution, the full sweep preserves it. This proves correctness of the stationary law without analyzing every path of the composed chain.

For kernels between different spaces, the invariant notion requires a self-kernel because the initial and resulting measures must share a state space. For a transition between `α` and `β`, express preservation as `μ.bind κ = ν` instead; do not force the endpoints into a single invariant predicate.

## 6. Invariance through test functions

Measure equality can be checked through integrals. If `μ` is invariant under `κ`, then for a suitable measurable nonnegative function `g`,

\[
  \int g(y)\,d\mu(y)
  =\int\left(\int g(y)\,d\kappa(x)(y)\right)d\mu(x).
\]

The inner integral is the one-step transition operator applied to `g`. This identity says that averaging a test function under the stationary law gives the same result before and after one random transition.

This form is convenient for expectations, harmonic functions, and energy estimates. It can also prove measure invariance when a class of test functions determines measures. The exact theorem requires measurability and integrability or nonnegativity assumptions; use a lintegral identity for extended nonnegative functions and a Bochner integral identity for integrable vector-valued functions.

When a proof goal is a measure equality, do not begin by expanding both measures on every measurable set unless that is the simplest route. First look for an integral characterization or a kernel-composition theorem that already provides the desired test-function identity.

## 7. Invariance, reversibility, and irreducibility

Invariance describes a distribution that is unchanged by one transition. Reversibility adds symmetry of flow. Irreducibility, from Chapter 44, says the kernel can reach every target set of positive reference measure from every starting state. None of these conditions alone implies all the others.

A reversible kernel is invariant when it is Markov. An invariant kernel need not be reversible; a directed cycle with uniform transition probabilities preserves the uniform distribution but has one-way flow around the cycle. Irreducibility can hold for both reversible and nonreversible chains.

In finite state spaces, irreducibility guarantees uniqueness of a stationary probability measure, while reversibility supplies a convenient way to construct one. Convergence to stationarity may still fail for a periodic chain. Keep the logical dependencies separate: prove each property, then apply a theorem whose statement includes the exact combination needed.

For example, the deterministic cycle on three states preserves the uniform measure and is irreducible. It is not reversible: each state sends all its mass clockwise, while the reverse transition has probability zero. Starting at one state, its distribution cycles through point masses and does not converge in total variation, even though the uniform measure is invariant and unique. This example is a useful counterexample when a proof has accidentally promoted stationarity or irreducibility into a convergence claim.

In a formal development, the finite-state uniqueness theorem and a convergence theorem should have separate wrappers with separate hypotheses. Uniqueness is a statement about the solution space of `πP = π`; convergence concerns the iterates `μP^n` and typically needs an aperiodicity or stronger mixing condition.

## 8. Composition preserves stationarity, but may destroy reversibility

If `κ` and `η` are Markov kernels and both preserve `π`, applying first `κ` and then `η` still preserves `π`: after the first step the law is `π`, and the second step leaves it unchanged. In Mathlib, `Kernel.Invariant.comp` captures this compositional fact. It is especially useful when a transition is implemented as several substeps, such as updating one coordinate at a time.

Reversibility behaves differently. Let `κ*` denote the time-reversal kernel relative to `π`; detailed balance says that a reversible kernel equals its own reversal. The reversal of a composition has the factors in the opposite order. Thus a composition of two reversible kernels is always stationary with respect to `π`, but it is generally reversible only when the factors commute or when some additional symmetry makes the two orders agree.

This distinction has a practical consequence for algorithms. A sequence of individually reversible coordinate updates preserves the target distribution, even when the full sweep through all coordinates is not reversible. In formal proofs, establish invariance of each update and compose those facts. Prove reversibility of the combined transition only if it is actually needed and the order argument supports it.

## 9. Lifting finite-state equations to kernel predicates

On a finite discrete state type, every measure is determined by its point masses and every set integral becomes a finite sum. This gives a controlled bridge from matrix calculations to `Kernel.Invariant` and `Kernel.IsReversible`. For stationarity, prove the coordinate equations

\[
  \pi(y)=\sum_x \pi(x)P(x,y)
\]

for each destination `y`; then sum over `y` in an arbitrary set. For reversibility, prove the pointwise flow equation for each pair `(x,y)` and sum over `x` in `A`, `y` in `B`. Reordering the two finite sums yields the swapped flow identity.

In Lean, introduce the finite sums as named lemmas before proving the abstract predicates. Use `Fintype` and `Finset.univ` to state the coordinate sums, and keep nonnegativity and row-sum-one obligations alongside the definition of the kernel. `simp` is effective for reducing membership in a concrete `Fin n`, but the algebraic equality of sums is usually clearer with an explicit `Finset.sum_congr` and a separate sum-reordering lemma.

This method is ideal for finite examples and counterexamples. For an infinite countable space, the corresponding sums may be infinite and require summability or Tonelli-type arguments. For a continuous space, pointwise transition densities need reference measures and measurable integral reasoning. The finite derivation teaches the shape of the argument, while the kernel predicate lets the general theorem avoid committing to one representation.

## 10. A proof workflow

1. Define the state space, transition kernel, and candidate measure.
2. Prove `IsMarkovKernel` if the rows should be probability measures.
3. For stationarity, establish `μ.bind κ = μ` or use a measure-determining integral identity.
4. For reversibility, start with detailed balance on simple sets or singleton atoms.
5. Apply `Kernel.IsReversible.invariant` to obtain invariance.
6. Use `Kernel.Invariant.comp` for composed transitions.
7. Combine with irreducibility or aperiodicity only after proving those separate properties.

In finite spaces, it is usually most efficient to reduce the measure equations to finite sums and simplify algebra after the probabilistic structure is established. In general spaces, preserve the kernel and integral abstractions rather than converting them prematurely into pointwise densities.

## 11. Common failure modes

### Stationarity is confused with a fixed state

An invariant measure is a fixed distribution under the transition, not a samplewise constant path.

### Detailed balance is used without the Markov property

The standard theorem deriving invariance assumes a Markov kernel. Supply total mass one.

### Reversibility is assumed from invariance

Invariance is a global balance equation. Reversibility requires pairwise flow symmetry and is strictly stronger.

### A uniform law is assumed for every random walk

On irregular graphs, degree-weighted measure is the natural reversible law.

### A one-step result is used for a composite chain without proof

Use the invariant-composition theorem or induct on kernel powers.

### Invariance is confused with convergence

An invariant law need not be unique, and the chain's marginal law need not converge to it without additional hypotheses.

## 12. Exercises

1. State `Kernel.Invariant κ μ` in terms of kernel binding.
2. Write detailed balance for measurable sets and for singleton states in a discrete chain.
3. Verify the stationary distribution of the two-state chain.
4. Prove that the degree-weighted measure is reversible for a simple random walk on an undirected graph.
5. Explain why reversibility implies invariance for a Markov kernel.
6. Show that a common invariant measure is preserved by composition of kernels.
7. Give a nonreversible kernel that preserves a measure.
8. Distinguish invariance, reversibility, irreducibility, and convergence.
9. Express invariance as an identity on integrals of nonnegative test functions.
10. Locate `Kernel.Invariant.comp` and `Kernel.IsReversible.invariant` in Mathlib's documentation.
11. Show that a one-way three-state cycle preserves the uniform distribution but fails detailed balance.
12. Explain why a composition of two invariant kernels remains invariant while reversibility of the composition needs an order condition.
13. Give the test-function identity associated with invariance and state one sufficient class of functions for which it is meaningful.

## Summary

An invariant measure satisfies `μ.bind κ = μ`. Reversibility is detailed balance: the measure flow from one set to another matches the reverse flow. For Markov kernels, reversibility implies invariance. Invariant measures persist under composition, and finite-state examples reduce to matrix equations. Stationarity, reversibility, irreducibility, and convergence are distinct properties that should be proved and used separately.

## Further reading

- [Mathlib: Kernel invariance and reversibility](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Invariance.html)
- [Mathlib: Kernel composition](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html)
- Chapters 40 and 44 for transition kernels and irreducibility.
- Chapter 46 for measure-preserving dynamics and ergodicity, and Chapter 48 for quantitative convergence in total variation.
