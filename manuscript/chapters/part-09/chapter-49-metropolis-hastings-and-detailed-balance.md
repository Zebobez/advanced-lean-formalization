# Chapter 49 — Metropolis–Hastings and Detailed Balance

> **Audience.** This chapter assumes familiarity with finite Markov kernels, probability weights, invariance, and reversibility. It formalizes the finite-state Metropolis–Hastings construction from unnormalized target weights and an arbitrary proposal matrix.

Markov chain Monte Carlo begins with a target distribution that is easy to evaluate up to a constant but difficult to sample from directly. Metropolis–Hastings turns a proposal mechanism into a new chain whose stationary distribution is the target. The central proof is detailed balance: accepted flow from `x` to `y` is exactly the smaller of the two opposing weighted proposal flows.

This chapter develops that calculation on a finite state type. The finite setting makes positivity, row sums, and ratios explicit, while preserving the main proof pattern used by the general theory. Mathlib already supplies kernels, reversibility, and the theorem that a reversible Markov kernel preserves its reference measure. The finite construction can therefore be proved with elementary sums and connected to those abstract predicates after its stochastic properties are established.

## Learning objectives

By the end of the chapter, you should be able to:

- construct a finite Metropolis–Hastings transition matrix from positive weights and a proposal kernel;
- avoid the unknown partition function by using unnormalized weights;
- prove the Metropolis–Hastings kernel is Markov and reversible;
- use reversibility to obtain invariance;
- identify proposal-support conditions needed for irreducibility;
- distinguish stationarity from actual convergence of the sampler.

## 1. Target weights and proposal kernels

Let `S` be a finite state type. A target distribution is specified by a weight function `w : S → ℝ` satisfying `0 < w(x)` for every state. Its normalizing constant is

\[
  Z=\sum_{x\in S}w(x),
  \qquad
  \pi(x)=\frac{w(x)}{Z}.
\]

In many applications `Z` is expensive to compute, while ratios of target weights are available. The Metropolis–Hastings transition will only use `w(y)/w(x)`, so no proof needs to evaluate `Z` beyond establishing that `π` is a probability measure.

A proposal kernel is a stochastic matrix `Q(x,y)` with nonnegative entries and each row summing to one. From the current state `x`, first draw a proposed state `y` according to `Q(x,·)`. A second random choice decides whether to accept the proposal. If it is rejected, the chain remains at `x`.

The proposal does not need to be symmetric. An asymmetric proposal is corrected by a ratio involving both directions, `Q(x,y)` and `Q(y,x)`. This is exactly why detailed balance is a convenient correctness proof: it compares the weighted flow of both proposed directions rather than trying to show the transition matrix itself is symmetric.

## 2. The off-diagonal transition formula

For distinct states `x` and `y`, define the Metropolis–Hastings transition probability by

\[
  K(x,y)=\min\left(Q(x,y),\frac{w(y)Q(y,x)}{w(x)}\right).
\]

Because `w(x)>0`, the expression is defined. The diagonal entry absorbs all probability not used by off-diagonal moves:

\[
  K(x,x)=1-\sum_{y\ne x}K(x,y).
\]

This is equivalent to proposing from `Q` and rejecting some proposals. In fact `K(x,y)≤Q(x,y)`, so

\[
  \sum_{y\ne x}K(x,y)
  \leq \sum_{y\ne x}Q(x,y)
  =1-Q(x,x)\leq1.
\]

Thus the diagonal entry is nonnegative. Each row sums to one by construction, so `K` is a Markov kernel.

The usual acceptance-probability formula is recovered when `Q(x,y)>0`:

\[
  a(x,y)=\min\left(1,\frac{w(y)Q(y,x)}{w(x)Q(x,y)}\right),
  \qquad
  K(x,y)=Q(x,y)a(x,y).
\]

The minimum formula for `K(x,y)` is often better for formalization because it avoids a case split on a zero proposal probability. It also makes the flow identity a single algebraic simplification.

The diagonal has a direct algorithmic interpretation. For each proposed `y≠x`, the rejected portion is `Q(x,y)-K(x,y)`. Therefore

\[
  K(x,x)=Q(x,x)+\sum_{y\ne x}\bigl(Q(x,y)-K(x,y)\bigr).
\]

The first term is a proposal that already selected the current state; the sum is the total rejection probability. This expression proves nonnegativity transparently, while the leftover-mass definition makes the row-sum proof immediate. Choose whichever is more convenient for the main theorem, and prove their equality once as a helper lemma.

## 3. Detailed balance from a symmetric minimum

For distinct `x` and `y`, multiply the transition probability by the target mass:

\[
\begin{aligned}
  \pi(x)K(x,y)
  &=\frac{w(x)}{Z}
    \min\left(Q(x,y),\frac{w(y)Q(y,x)}{w(x)}\right)\\
  &=\frac1Z\min\left(w(x)Q(x,y),w(y)Q(y,x)\right).
\end{aligned}
\]

The final expression is symmetric in `x` and `y`, so

\[
  \pi(x)K(x,y)=\pi(y)K(y,x).
\]

On the diagonal, detailed balance is tautological. Therefore the target is reversible with respect to the Metropolis–Hastings kernel. Since the kernel is Markov, `Kernel.IsReversible.invariant` yields that `π` is invariant.

This is a textbook example of choosing a representation to make the proof linear. Proving the displayed identity directly is much easier than expanding `π.bind K` and showing every coordinate returns to its original value. The abstract reversibility theorem then lifts the pointwise finite flow equality to the measure-level definition over measurable sets.

## 4. Worked example: a two-state target

Let `S={0,1}` with unnormalized weights `w(0)=1` and `w(1)=3`. Use the proposal that always flips the state:

\[
  Q(0,1)=Q(1,0)=1.
\]

The target distribution is `π(0)=1/4`, `π(1)=3/4`. The off-diagonal transitions are

\[
  K(0,1)=\min(1,3)=1,
  \qquad
  K(1,0)=\min(1,1/3)=1/3.
\]

The diagonal entries are `K(0,0)=0` and `K(1,1)=2/3`. Detailed balance reduces to

\[
  \pi(0)K(0,1)=\frac14
  =\frac34\cdot\frac13=\pi(1)K(1,0).
\]

The transition matrix is visibly not symmetric, but the weighted flow is symmetric. The chain is irreducible. It is also aperiodic because state `1` has a positive probability of remaining in place. Starting from state `0`, after one step the law is concentrated on state `1`, and thereafter it converges to the target distribution.

In Lean, use `Fin 2`, define the four matrix entries, and prove the target normalization separately. A useful helper lemma is the generic identity

\[
  a\min(b,c/a)=\min(ab,c),\quad a>0,
\]

in the appropriate ordered field. Once this identity is available, detailed balance for all state pairs becomes a short finite case split.

## 5. Worked example: an asymmetric proposal

Let the state space be `{0,1,2}` and consider a proposal that moves clockwise with probability one: `0→1`, `1→2`, `2→0`. For any strictly positive target weights, the reverse proposal probability is zero for each clockwise edge. The Metropolis–Hastings formula therefore assigns zero accepted probability to every such move. The diagonal absorbs the whole row, and the resulting chain stays at its initial state forever.

This is not a defect in detailed balance. It is a reminder that correction cannot create transitions that have no reverse proposal support. For distinct states, `K(x,y)>0` exactly when both `Q(x,y)>0` and `Q(y,x)>0`, assuming the target weights are strictly positive. The effective movement graph consists of mutually proposed edges.

The example is useful as a formal counterexample: a correct invariant law does not imply that a particular initialization will sample from it. The chain above preserves every probability measure because it is the identity kernel, but it does not move toward the selected target from an arbitrary initial state.

### Symmetric proposals recover the Metropolis rule

If `Q(x,y)=Q(y,x)`, the acceptance probability for a supported proposal reduces to

\[
  a(x,y)=\min\left(1,\frac{w(y)}{w(x)}\right).
\]

The proposal's asymmetry correction disappears, but the same flow proof still applies:

\[
  w(x)K(x,y)=Q(x,y)\min(w(x),w(y)).
\]

This is the original Metropolis form. It is a useful special case for simplifying finite examples, but the general Hastings formula should remain the reusable definition. In a formal library, prove the symmetric simplification as a theorem derived from the general kernel rather than defining a second unrelated chain.

The acceptance probability is not a measure of overall algorithm quality by itself. Accepting every proposal can produce a chain that moves rapidly but may be poorly structured; rejecting many proposals can preserve the target while making mixing slow. The theorem-level correctness property is detailed balance, while efficiency requires separate analysis such as the coupling and spectral estimates of Chapter 48.

## 6. Proposal support, irreducibility, and self-loops

On a finite state space with strictly positive target weights, the transition graph of the Metropolis–Hastings kernel has an edge from `x` to `y`, for `x≠y`, exactly when the proposal supports both directions. Thus if the undirected graph of mutually supported proposal edges is connected, the resulting finite chain is irreducible.

The diagonal probability includes rejected proposals and any proposal mass already assigned to `x`. A positive rejection probability at a state creates a self-loop there. To establish aperiodicity for a finite irreducible chain, it is sufficient to show a self-loop at one state; irreducibility propagates period one to all states. This is a separate argument from detailed balance and invariance.

For a target supported on only part of the state space, the cleanest finite development is often to subtype the positive support and work with a strictly positive weight there. If zero-weight states remain in the ambient type, the proposal may enter them and the ratio formula must specify what happens. Avoid dividing by zero and state clearly whether the algorithm is defined only on the support or on the whole space.

## 7. Unnormalized weights and proof boundaries

Suppose the target is only known up to a constant factor: `w'(x)=c w(x)` with `c>0`. The Metropolis–Hastings transition is unchanged because

\[
  \frac{w'(y)Q(y,x)}{w'(x)Q(x,y)}
  =\frac{cw(y)Q(y,x)}{cw(x)Q(x,y)}
  =\frac{w(y)Q(y,x)}{w(x)Q(x,y)}.
\]

The stationary probability is also unchanged after normalization. This scale-invariance is central to applications where the partition function is unknown.

Formalize scale invariance as a separate theorem about the transition entries. Then reuse the theorem for target weights, rather than carrying a normalizing constant through every proposal calculation. Likewise, isolate these proof layers:

1. `w` is strictly positive and has a positive finite sum.
2. `π` is the normalized probability measure built from `w`.
3. `Q` has nonnegative entries and each row sums to one.
4. `K` has nonnegative entries and each row sums to one.
5. The pairwise weighted-flow equation holds.
6. Reversibility implies invariance.

This layered design keeps the numerical identities separate from the kernel abstractions. It also makes later modifications—different proposals, state encodings, or target weights—local.

## 8. From finite matrices to Mathlib kernels

For a finite discrete state space, interpret each row `K(x,·)` as a probability measure and package those rows as a kernel. Prove the Markov-kernel property from nonnegativity and the row-sum-one equation. Then prove pairwise detailed balance and lift it to the set-integral formulation of `Kernel.IsReversible` by finite summation.

There are two practical representations for the target. A probability measure makes the invariant-law theorem immediate, while a finite weight vector makes the acceptance calculation simpler. A clean development can keep both: define `π` from normalized weights, prove its atom formula, and use that formula only in the pairwise calculation. Do not unfold the construction of the probability measure in every case split.

When lifting the pairwise identity, split the double sum over `A × B` and use finite-sum congruence. The diagonal terms agree automatically; the off-diagonal terms use the flow equation. This is a small proof, but stating it once as a generic finite-kernel lemma makes many later algorithms easier to verify.

The final step is intentionally abstract. Once reversibility is established, apply the general theorem from Chapter 45 rather than reproving `π.bind K=π` coordinate by coordinate. This gives a reusable boundary: a finite construction proves a property of a kernel, and the kernel API supplies the general consequences.

Keep the coercions between natural numbers, reals, and extended nonnegative reals localized. Transition probabilities and target weights are often represented in `ℝ`, while measure values may use `ℝ≥0∞`. Prove the finite scalar identities in one ordered field, then convert the resulting nonnegative values when building measures. This avoids mixing `ENNReal` division lemmas into the acceptance-ratio calculation.

The general measurable-space Metropolis–Hastings construction can require densities, Radon–Nikodym derivatives, and careful treatment of singular proposal components. The finite proof should not be presented as if those obligations vanish in a continuous space. It instead demonstrates the central balance equation in a setting where all terms are explicit finite sums.

## 9. Stationarity is not a sampling guarantee

Reversibility proves the target distribution is invariant. It does not prove that the chain reaches that distribution from every starting state, that the stationary distribution is unique, or that empirical averages are accurate at a finite time. For those claims, establish irreducibility, aperiodicity, and a quantitative convergence condition such as the minorization or coupling estimates from Chapter 48.

If the chain is initialized with law `π`, every later state has law `π`; this is an exact statement about each marginal. If it starts at a fixed state, its distribution generally differs from `π` for an initial period. Monte Carlo estimates from a finite run therefore involve both convergence and sampling variability, topics not settled by detailed balance alone.

In formal statements, distinguish `Kernel.Invariant`, uniqueness of invariant probability, convergence in total variation, and convergence of empirical averages. A theorem proving one of these should not have a name or conclusion that suggests all four.

## 10. A proof workflow

1. Choose the finite state type and a strictly positive unnormalized target weight.
2. Define the proposal matrix and prove its rows are probability vectors.
3. Define off-diagonal transitions by the minimum-of-flows formula.
4. Define each diagonal entry as the remaining row mass.
5. Prove nonnegativity and the row-sum-one property.
6. Derive the symmetric minimum identity for the weighted flow.
7. Lift pointwise detailed balance to `Kernel.IsReversible`.
8. Apply the reversibility-implies-invariance theorem.
9. Prove support connectivity and aperiodicity separately if convergence is needed.
10. Use Chapter 48's contraction or coupling methods for a quantitative rate.

## 11. Common failure modes

### The unknown normalization constant is carried everywhere

Work with unnormalized weights in the transition formula; the partition function cancels from the flow identity.

### An asymmetric proposal is treated as symmetric

The reverse proposal probability belongs in the acceptance ratio.

### Zero proposal probabilities are divided by

Use the minimum-of-flows formula for off-diagonal transitions, or explicitly separate the zero-proposal case.

### The diagonal probability is guessed

Define it as the leftover mass and prove the off-diagonal sum is at most one.

### Correctness is inferred from invariance

The identity kernel preserves the target but never explores the state space. Establish reachability and convergence separately.

### Proposal connectivity is assumed to survive correction

With positive target weights, Metropolis–Hastings keeps only mutually supported proposal edges. Check the resulting movement graph.

### Almost-sure sampling language is inferred from a stationary law

Invariance describes marginals when started in stationarity; it does not bound finite-run error from an arbitrary start.

## 12. Exercises

1. Define the finite Metropolis–Hastings transition from positive weights and a proposal matrix.
2. Prove each diagonal transition probability is nonnegative.
3. Derive the detailed-balance identity using the symmetric minimum of opposing flows.
4. Compute the two-state example with target weights `1` and `3` and a flip proposal.
5. Explain why a one-way directed cycle proposal produces no accepted off-diagonal moves.
6. State the mutual-support condition for positive off-diagonal transitions.
7. Show that multiplying every target weight by the same positive constant leaves the chain unchanged.
8. Identify which properties follow from reversibility and which require irreducibility or aperiodicity.
9. Explain how the finite detailed-balance proof is lifted to `Kernel.IsReversible`.
10. Locate `Kernel.IsReversible.invariant` in Mathlib's documentation.

## 13. Lean formalization

The central scalar lemma below turns the minimum-of-flows formula into a symmetric weighted flow.
The positivity assumption on the current state's target weight justifies cancellation of its
denominator. The rational example checks the asymmetric two-state chain exactly, and the final
wrapper records the library-level consequence that reversibility implies invariance for a Markov
kernel.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def acceptProposal (proposal target : Nat) : Nat :=
  if proposal ≤ target then proposal else target

theorem symmetricMinimumAcceptsTheSmallerWeight : acceptProposal 2 1 = 1 := by decide
```

```lean
theorem exercise_49_3_weighted_acceptance_flow
    (wx wy qxy qyx : ℝ) (hwx : 0 < wx) :
    wx * min qxy (wy * qyx / wx) = min (wx * qxy) (wy * qyx) := by
  calc
    wx * min qxy (wy * qyx / wx) =
        min (wx * qxy) (wx * (wy * qyx / wx)) := by
      rw [mul_min_of_nonneg qxy (wy * qyx / wx) hwx.le]
    _ = min (wx * qxy) (wy * qyx) := by
      congr 1
      field_simp

theorem exercise_49_3_weighted_flow_symmetric
    (wx wy qxy qyx : ℝ) (hwx : 0 < wx) (hwy : 0 < wy) :
    wx * min qxy (wy * qyx / wx) = wy * min qyx (wx * qxy / wy) := by
  calc
    wx * min qxy (wy * qyx / wx) = min (wx * qxy) (wy * qyx) :=
      exercise_49_3_weighted_acceptance_flow wx wy qxy qyx hwx
    _ = min (wy * qyx) (wx * qxy) := min_comm _ _
    _ = wy * min qyx (wx * qxy / wy) :=
      (exercise_49_3_weighted_acceptance_flow wy wx qyx qxy hwy).symm

def mhAcceptanceRational (wx wy qxy qyx : ℚ) : ℚ :=
  min qxy (wy * qyx / wx)

theorem exercise_49_4_forward_acceptance :
    mhAcceptanceRational 1 3 1 1 = 1 := by
  norm_num [mhAcceptanceRational]

theorem exercise_49_4_reverse_acceptance :
    mhAcceptanceRational 3 1 1 1 = 1 / 3 := by
  norm_num [mhAcceptanceRational]

theorem exercise_49_4_detailed_balance :
    1 * mhAcceptanceRational 1 3 1 1 =
      3 * mhAcceptanceRational 3 1 1 1 := by
  norm_num [mhAcceptanceRational]

theorem exercise_49_5_one_way_proposal_is_rejected
    (wx wy qxy : ℝ) (hqxy : 0 ≤ qxy) :
    min qxy (wy * (0 : ℝ) / wx) = 0 := by
  simp [hqxy]
```

```lean
theorem exercise_49_10_reversible_markov_kernel_is_invariant
    {α : Type*} [MeasurableSpace α] {κ : ProbabilityTheory.Kernel α α}
    [ProbabilityTheory.IsMarkovKernel κ] {π : MeasureTheory.Measure α}
    (hrev : ProbabilityTheory.Kernel.IsReversible κ π) :
    ProbabilityTheory.Kernel.Invariant κ π :=
  hrev.invariant
```

## Summary

Metropolis–Hastings adjusts a proposal so that the target-weighted flow in each direction is the same. The finite off-diagonal transition is the minimum of the two opposing weighted proposal flows, and a leftover diagonal term makes each row stochastic. Reversibility then gives invariance through Mathlib's kernel theorem. Support, aperiodicity, and convergence remain separate obligations; correctness of the stationary law alone is not a guarantee that a finite run has mixed.

## Further reading

- [Mathlib: Kernel invariance and reversibility](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Invariance.html)
- [Hastings, “Monte Carlo sampling methods using Markov chains and their applications”](https://academic.oup.com/biomet/article/57/1/97/284580)
- Chapters 45 and 48 for detailed balance, invariance, and convergence bounds.
