# Chapter 50 — Gibbs Sampling and Conditional Kernels

> **Audience.** This chapter assumes familiarity with finite product spaces, conditional probability, disintegration, and reversible Markov kernels. It formalizes coordinate and block Gibbs updates and explains why scan order affects reversibility.

Gibbs sampling builds a Markov chain by repeatedly replacing part of a state with a draw from its conditional distribution given the remaining coordinates. Each update preserves the target joint distribution. This gives a direct correctness proof when the conditional laws are easier to represent than a global proposal ratio.

The main formalization challenge is to keep the conditioning context fixed while the updated coordinate varies. In a finite product space, the conditional distribution is an explicit normalized slice of the target weights. In a general probability space, conditional kernels arise through disintegration and are usually specified only almost everywhere with respect to the marginal. The finite derivation gives a concrete model for that more abstract interface.

## Learning objectives

By the end of the chapter, you should be able to:

- define a coordinate Gibbs kernel on a finite product space;
- prove that its rows are probability measures;
- prove reversibility by comparing joint mass before and after an update;
- distinguish random-scan mixtures from systematic-scan compositions;
- identify support and conditioning-null-set issues;
- connect finite conditional tables to Mathlib's conditional-kernel interface.

## 1. Conditional distributions as transition rules

Let the state space be a product `X × Y` with target probability `π`. A Gibbs update of the `X` coordinate leaves `y` fixed and redraws `x` from the conditional law of `X` given `Y=y`. The resulting kernel is

\[
  K_X((x,y),(x',y'))
  =\mathbf{1}_{y'=y}\,\pi(X=x'\mid Y=y).
\]

The old value `x` does not affect the conditional draw except through the preserved coordinate `y`. A `Y`-coordinate update is defined symmetrically.

On a finite state space with strictly positive unnormalized weights `w(x,y)`, define the marginal slice weight

\[
  w_Y(y)=\sum_{x\in X}w(x,y),
\]

and the conditional probability

\[
  \pi(X=x\mid Y=y)=\frac{w(x,y)}{w_Y(y)}.
\]

The global partition function cancels. Strict positivity ensures every slice normalizer is positive, so the conditional is defined at every context. If the target has zero-probability contexts, the conditional can be chosen arbitrarily there without changing the joint law; a formal development must represent that almost-everywhere freedom explicitly or restrict to positive support.

## 2. The coordinate-update kernel is Markov

For each fixed `y`, the conditional probabilities sum to one:

\[
  \sum_{x'\in X}\frac{w(x',y)}{w_Y(y)}=1.
\]

The update kernel assigns mass only to states with the same `Y` coordinate, and the mass over all possible replacement `X` coordinates is one. Thus each row is a probability distribution.

The proof should be organized around the unchanged context. First fix a source state `(x,y)`, then sum the kernel over all target pairs `(x',y')`. All terms with `y'≠y` vanish; the remaining sum is exactly the conditional normalization identity above.

For a product of more than two coordinates, treat all coordinates other than `i` as one context `x_{-i}`. This avoids writing a separate proof for each dimension. A block update is identical: choose a subset of coordinates to resample jointly from their conditional law given the complementary block.

In Lean, a helper function that extracts the context and replaces one coordinate can clarify dependent tuple manipulation. Prove the replacement operation is a bijection between the set of states with a fixed context and the coordinate type; then use that bijection to evaluate the row sum.

For an indexed product `∀ i, X i`, the context is a function on all indices except the chosen coordinate. Encoding this as a subtype or as a product over a smaller index type is often preferable to ad hoc tuple reassociation. The update map then changes exactly one component. Extensionality reduces equality of two updated states to equality at each coordinate, with the selected coordinate handled by the replacement value and every other coordinate handled by the fixed context.

## 3. Detailed balance for a Gibbs update

Take two states `s=(x,y)` and `t=(x',y')`. If `y≠y'`, neither state can transition to the other under an `X` update, so both sides of detailed balance are zero. If `y=y'`, then

\[
\begin{aligned}
  \pi(x,y)K_X((x,y),(x',y))
  &=\pi(x,y)\pi(X=x'\mid Y=y)\\
  &=\pi_Y(y)\pi(X=x\mid Y=y)\pi(X=x'\mid Y=y).
\end{aligned}
\]

The expression is symmetric in `x` and `x'`. Therefore

\[
  \pi(s)K_X(s,t)=\pi(t)K_X(t,s).
\]

The coordinate-update kernel is reversible with respect to the joint target. By Chapter 45, it is also invariant. The same proof applies to every coordinate or block update.

This derivation reveals the role of conditional probability: it factors the joint mass into a context marginal and a conditional law. Once the context is fixed, the two replacement coordinates appear symmetrically as two factors of the same conditional distribution.

## 4. Worked example: a two-coordinate target

Let `X=Y={0,1}` and use unnormalized weights

\[
  \begin{array}{c|cc}
       & y=0 & y=1\\ \hline
  x=0  & 1 & 3\\
  x=1  & 2 & 4
  \end{array}
\]

The total weight is `10`. For an `X` update, the conditionals are

\[
  \mathbb{P}(X=1\mid Y=0)=\frac23,
  \qquad
  \mathbb{P}(X=1\mid Y=1)=\frac47.
\]

For a `Y` update, they are

\[
  \mathbb{P}(Y=1\mid X=0)=\frac34,
  \qquad
  \mathbb{P}(Y=1\mid X=1)=\frac23.
\]

To check detailed balance for an `X` update, compare states `(0,0)` and `(1,0)`:

\[
  \pi(0,0)K_X((0,0),(1,0))
  =\frac1{10}\cdot\frac23=\frac1{15},
\]

while

\[
  \pi(1,0)K_X((1,0),(0,0))
  =\frac2{10}\cdot\frac13=\frac1{15}.
\]

The second update has the same property by the general argument. This example is large enough to expose conditioning but small enough that every transition can be inspected by finite computation.

For formalization, define the weight table and prove each marginal slice sum first. The four conditional probabilities then follow by simplification. A generic proof over `Fintype X` and `Fintype Y` is more reusable than a four-state enumeration, but the concrete table is valuable for checking the order and normalization of coordinates.

## 5. Random scan is a reversible mixture

Suppose each coordinate update `K_i` is reversible with respect to the same target `π`, and choose coordinate `i` with fixed probability `p_i`, where `p_i≥0` and `∑_i p_i=1`. The random-scan kernel is

\[
  K=\sum_i p_iK_i.
\]

Detailed balance is linear in the transition kernel, so

\[
  \pi(x)K(x,y)
  =\sum_i p_i\pi(x)K_i(x,y)
  =\sum_i p_i\pi(y)K_i(y,x)
  =\pi(y)K(y,x).
\]

Thus a fixed-probability mixture of reversible coordinate updates remains reversible. In Lean, prove the mixture is Markov and distribute the finite sum through the detailed-balance identity.

The scan probabilities should be independent of the current state for this simple argument. A state-dependent choice of coordinate can still be designed to preserve `π`, but reversibility requires a separate balance calculation that includes the selection probabilities in both directions.

Random scan is not automatically irreducible. If every coordinate can be selected but the conditional law assigns zero mass to some values, the chain may remain trapped in a component of the support. Prove reachability on the actual positive support, not merely on the ambient product type.

The scan mixture also has a transparent finite probability interpretation: sample an index `i` according to `(p_i)`, then apply `K_i`. In a kernel-based development, the mixture should be defined as a weighted sum of transition measures, not as a composition of kernels. The sum-of-weights-one proof establishes the Markov property; linearity then establishes detailed balance. This distinction prevents a common notational mistake in which a random choice of update is accidentally encoded as sequential execution of all updates.

## 6. Systematic scan preserves the target but can lose reversibility

A systematic sweep applies coordinate kernels in a fixed order, for example

\[
  K_{\mathrm{sweep}}=K_XK_Y.
\]

Each factor preserves `π`, so their composition preserves `π`. But the composition is not generally reversible, because time reversal reverses the factor order. This is the same distinction developed in Chapter 45: invariance composes, while reversibility of a composition needs an order condition.

For the table in Section 4, apply the `X` update and then the `Y` update. The probability of moving from `(0,0)` to `(1,0)` in one sweep is

\[
  K_{\mathrm{sweep}}((0,0),(1,0))=\frac23\cdot\frac13=\frac29.
\]

The reverse transition has probability

\[
  K_{\mathrm{sweep}}((1,0),(0,0))=\frac13\cdot\frac14=\frac1{12}.
\]

The weighted flows differ:

\[
  \frac1{10}\cdot\frac29=\frac1{45},
  \qquad
  \frac2{10}\cdot\frac1{12}=\frac1{60}.
\]

So the systematic sweep preserves the target but is not reversible. This is a concrete counterexample to the claim that a composition of reversible kernels is always reversible.

The proof pattern in Lean is modular: prove `K_X.Invariant π` and `K_Y.Invariant π`, compose their invariance proofs, then separately refute or prove reversibility of the combined kernel. Do not try to prove the stronger property when only stationarity is needed.

## 7. Conditional kernels and disintegration

For general measurable spaces, a joint measure on `X × Y` need not admit a pointwise conditional probability by elementary division. Disintegration supplies a conditional kernel `κ(y,·)` such that the joint measure is recovered by integrating the conditional law against the marginal of `Y`.

Mathlib's `Measure.IsCondKernel` and `Kernel.IsCondKernel` package the corresponding disintegration identities. For finite spaces, the conditional distribution is defined explicitly from the joint point masses whenever the marginal context has positive mass. For standard Borel spaces, Mathlib provides existence results under its stated finiteness and countability or standard-Borel assumptions.

The distinction between everywhere-defined and almost-everywhere-defined conditionals matters. A context with zero marginal probability has no uniquely determined conditional distribution. Different choices there induce the same joint measure. Formal proofs should use the conditional-kernel identity, which already respects this measure-theoretic equivalence, rather than trying to prove pointwise equality at null contexts.

For finite tables with zero-mass rows, one can choose any probability distribution as the conditional at a null context, for example a fixed Dirac measure. The row must still be a probability measure for the conditional object to be a Markov kernel, even though its value does not affect the reconstructed joint distribution. This is a useful separation between the totality required by the type and the almost-everywhere uniqueness supplied by the mathematics.

When a theorem only needs a finite model, keep the conditional weights explicit. When a theorem is intended to apply to general standard Borel spaces, use the disintegration interface and carry its almost-everywhere qualifications. A finite proof is an excellent specification test but does not establish the general existence theorem.

## 8. Connection to conditional independence

Gibbs updates use conditional distributions given all other coordinates. Conditional independence can simplify these conditionals. If the model factorizes according to a graph, a coordinate's conditional law may depend only on its neighboring variables. This makes local updates possible without recomputing a global joint weight.

For formalization, prove the factorization or conditional-independence statement first, then derive the local conditional law. Do not assume that a factorized expression automatically has a particular conditional distribution: normalizing constants and support restrictions still need proof. Chapters 41–43 supply the surrounding interfaces for disintegration, Bayesian conditionals, and conditional independence.

This separation helps both mathematical reasoning and computation. The probability theorem explains why a local update preserves the joint law; an implementation can then exploit sparsity by evaluating only the factors involving the selected coordinate.

For a factorization `w(x)=∏_{C} ψ_C(x_C)`, conditioning on all coordinates except `i` cancels every factor whose scope does not contain `i`. The remaining conditional weight is proportional to the product of factors involving `i`. This local expression can reduce computation dramatically, but the formal proof still needs to show that the omitted factors are constant with respect to the replacement coordinate and that the local normalizer is positive.

## 9. Gibbs sampling and convergence

Each Gibbs update preserves the target. That gives correctness at stationarity and allows arbitrary compositions or mixtures of invariant updates to retain the same target. It does not prove that the sequence of states reaches every relevant part of the support or converges from every initialization.

For convergence, analyze the graph whose edges connect states that can be related by a positive-probability coordinate update. If this graph is disconnected, the chain is reducible. If it is connected, the finite chain is irreducible; then check periodicity or establish a quantitative contraction. Chapter 48's total-variation methods apply after a suitable minorization or coupling has been proved.

The time average of an observable introduces another layer. An ergodic theorem can justify long-run Monte Carlo averages under integrability and ergodicity assumptions, but invariance of each update alone is not that theorem. Keep the correctness of the target, convergence of the chain, and error of a finite Monte Carlo estimate as separate claims.

## 10. A proof workflow

1. Define the product state space, target weight, and positive support.
2. Derive the marginal slice weights for each conditioning context.
3. Define the finite conditional distributions and prove they normalize.
4. Build one coordinate or block update kernel.
5. Prove its Markov property from the conditional row sums.
6. Prove detailed balance by factoring joint mass into marginal and conditional terms.
7. Use reversibility to obtain invariance.
8. For random scan, prove a fixed convex mixture remains reversible.
9. For systematic scan, compose invariance and check reversibility separately.
10. Establish support connectivity and quantitative convergence only if needed.

## 11. Common failure modes

### The conditioning context changes during a sum

Keep the coordinates held fixed explicit while summing over replacement values.

### A zero-mass context is divided by

Restrict to positive support or use a conditional kernel defined up to almost-everywhere equality.

### A coordinate update is assumed to be reversible without proof

Show the conditional factorization makes the weighted flow symmetric.

### A systematic sweep is called reversible

Composition preserves invariance, but the reversed order of updates can have different transition probabilities.

### State-dependent scan probabilities are treated as a fixed mixture

Include the selection probability in both directions of detailed balance.

### Correctness is confused with convergence

An invariant target does not imply irreducibility, aperiodicity, or a finite-time error bound.

## 12. Exercises

1. Define the finite Gibbs update of one coordinate on `X × Y`.
2. Prove the conditional row sums equal one.
3. Derive detailed balance for a coordinate update from the conditional factorization of the joint law.
4. Compute the conditionals for the four-state table in Section 4.
5. Prove that a fixed convex mixture of reversible kernels with a common invariant law is reversible.
6. Explain why a systematic sweep remains invariant.
7. Verify the numerical detailed-balance failure for the systematic sweep in Section 6.
8. State how a conditional kernel reconstructs a joint measure by disintegration.
9. Explain what freedom remains at a context of zero marginal probability.
10. Give a support-graph criterion that would establish irreducibility for a finite Gibbs chain.
11. Distinguish target invariance, chain convergence, and a Monte Carlo law of large numbers.
12. Locate `Measure.IsCondKernel` and `Kernel.IsCondKernel` in Mathlib's documentation.

## 13. Lean formalization

The finite calculations below check the conditional probabilities and the detailed-balance pair from
the worked table. The systematic-scan values provide a concrete witness that the sweep preserves
the target through composition while failing detailed balance. The final block uses Mathlib's
measure conditional kernel: it is a Markov kernel and reconstructs the original joint measure from
the context marginal and conditional law. This is the abstract disintegration boundary behind the
finite update formulas.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

theorem gibbsUpdateHasUniformRowAtZero : rowMass resetKernel zero = 2 :=
  reset_zero_row

theorem gibbsUpdateHasUniformRowAtOne : rowMass resetKernel one = 2 :=
  reset_one_row
```

```lean
theorem exercise_50_4_x_given_y_zero :
    (2 : ℚ) / (1 + 2) = 2 / 3 := by norm_num

theorem exercise_50_4_x_given_y_one :
    (4 : ℚ) / (3 + 4) = 4 / 7 := by norm_num

theorem exercise_50_4_y_given_x_zero :
    (3 : ℚ) / (1 + 3) = 3 / 4 := by norm_num

theorem exercise_50_4_y_given_x_one :
    (4 : ℚ) / (2 + 4) = 2 / 3 := by norm_num

theorem exercise_50_3_first_pair_detailed_balance :
    (1 : ℚ) / 10 * (2 / 3) = (2 : ℚ) / 10 * (1 / 3) := by
  norm_num

theorem exercise_50_7_systematic_sweep_forward_flow :
    (1 : ℚ) / 10 * ((2 : ℚ) / 3 * (1 / 3)) = 1 / 45 := by
  norm_num

theorem exercise_50_7_systematic_sweep_reverse_flow :
    (2 : ℚ) / 10 * ((1 : ℚ) / 3 * (1 / 4)) = 1 / 60 := by
  norm_num

theorem exercise_50_7_systematic_sweep_is_not_reversible_at_pair :
    (1 : ℚ) / 45 ≠ 1 / 60 := by
  norm_num
```

```lean
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

theorem exercise_50_6_invariant_updates_compose
    {α : Type*} [MeasurableSpace α] {κ η : Kernel α α} {μ : Measure α}
    (hκ : Kernel.Invariant κ μ) (hη : Kernel.Invariant η μ) :
    Kernel.Invariant (κ ∘ₖ η) μ :=
  Kernel.Invariant.comp hκ hη

theorem exercise_50_8_measure_conditional_kernel_is_markov
    {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (ρ : Measure (Y × X)) [IsFiniteMeasure ρ] :
    IsMarkovKernel (ρ.condKernel : Kernel Y X) := by
  infer_instance

theorem exercise_50_8_conditional_kernel_reconstructs_joint
    {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (ρ : Measure (Y × X)) [IsFiniteMeasure ρ] :
    ρ.fst ⊗ₘ ρ.condKernel = ρ :=
  ρ.disintegrate ρ.condKernel
```

## Summary

Gibbs sampling replaces a coordinate or block with a draw from its conditional law. The conditional normalization proves the update is Markov, and factoring joint mass into marginal and conditional terms proves detailed balance. Fixed mixtures of reversible updates stay reversible; systematic compositions stay invariant but may lose reversibility. General conditional kernels arise through disintegration and are identified only almost everywhere at null contexts. As with other MCMC methods, invariance is a correctness property, while support and convergence require separate arguments.

## Further reading

- [Mathlib: Kernel disintegration and conditional kernels](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Disintegration/Basic.html)
- [Mathlib: Standard-Borel disintegration](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Disintegration/StandardBorel.html)
- Chapters 41–45 for conditional kernels, conditional independence, invariance, and reversibility.
- Chapter 48 for total-variation contraction and mixing bounds.
