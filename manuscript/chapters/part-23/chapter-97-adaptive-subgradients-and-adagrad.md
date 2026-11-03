# Chapter 97 — Adaptive Subgradients and AdaGrad

> **Audience.** This chapter assumes online convex optimization, mirror descent, and stochastic-gradient methods from Chapters 94–96. It studies diagonal adaptive geometry: a method that assigns a different effective learning rate to each coordinate using the gradients observed so far.

A single global learning rate treats every direction as if it had the same scale and activity. In high-dimensional sparse problems, a coordinate may appear rarely but carry a large signal, while another is updated on nearly every round. AdaGrad adapts the geometry to the observed sequence by accumulating squared gradients coordinate by coordinate.

The central proof is a variable-metric mirror-descent argument. A weighted projection gives a one-round potential inequality; monotonic growth of the diagonal metric still permits telescoping; and the cumulative gradient magnitudes bound the remaining dual-norm terms. The result is a regret guarantee that records which coordinates were active and how strongly.

## Learning objectives

After this chapter, you should be able to:

- define diagonal AdaGrad from cumulative squared gradients;
- derive its weighted projection certificate and coordinatewise regret bound;
- explain why positivity and monotonicity of the adaptive metric are proof invariants;
- distinguish an online regret theorem from a stochastic expected-risk theorem;
- compare diagonal adaptation with full-matrix adaptation and a global learning rate;
- formalize a changing diagonal metric using finite sums and coordinatewise order.

## 1. Why adapt the geometry?

Consider online convex losses \(f_1,\ldots,f_T\) on a nonempty compact convex set \(X\subset\mathbb R^d\). At round \(t\), the algorithm chooses \(x_t\), observes a subgradient \(g_t\in\partial f_t(x_t)\), and updates. Convexity gives

\[
f_t(x_t)-f_t(u)\le\langle g_t,x_t-u\rangle
\]

for every comparator \(u\in X\).

Ordinary projected gradient descent uses the Euclidean geometry for every round. Its regret proof depends on a bound on \(\|x_t-u\|_2\) and on the full gradient norm \(\|g_t\|_2\). This can obscure useful structure. If the gradients are sparse, or their coordinate magnitudes differ greatly, the cumulative geometry is anisotropic.

For each coordinate \(i\), define the accumulated scale

\[
h_{t,i}=\sqrt{\delta^2+\sum_{s=1}^t g_{s,i}^2},
\qquad \delta>0.
\tag{97.1}
\]

The stabilizer \(\delta\) makes every scale strictly positive from the first round. Let \(H_t\) be the diagonal matrix with entries \(h_{t,i}\). After observing \(g_t\), choose

\[
x_{t+1}
=\arg\min_{x\in X}\left\{
\eta\langle g_t,x\rangle
+\frac12\|x-x_t\|_{H_t}^2
\right\},
\tag{97.2}
\]

where \(\|z\|_{H_t}^2=z^\mathsf T H_t z\), and \(\eta>0\). The effective unconstrained coordinate step is

\[
x_{t+1,i}=x_{t,i}-\frac{\eta g_{t,i}}{h_{t,i}}.
\tag{97.3}
\]

A coordinate with a large history of squared gradients receives a smaller step. A rarely active coordinate keeps a larger step available. The metric is chosen from observed gradients, so the update is made after the current loss has supplied \(g_t\).

## 2. A variable-metric mirror-descent inequality

The update (97.2) is a proximal step in the \(H_t\)-geometry. Since \(H_t\) is positive definite, the objective is strictly convex; compactness of \(X\) gives a minimizer. For every \(u\in X\), first-order optimality yields

\[
\left\langle
\eta g_t+H_t(x_{t+1}-x_t),\,u-x_{t+1}
\right\rangle\ge0.
\tag{97.4}
\]

The weighted three-point identity is

\[
\|u-x_t\|_{H_t}^2-\|u-x_{t+1}\|_{H_t}^2
-\|x_{t+1}-x_t\|_{H_t}^2
=2\langle H_t(x_{t+1}-x_t),u-x_{t+1}\rangle.
\tag{97.5}
\]

Pair (97.4) with the comparator and use (97.5). Then split the loss pairing at the updated point:

\[
\langle g_t,x_t-u\rangle
=\langle g_t,x_t-x_{t+1}\rangle
+\langle g_t,x_{t+1}-u\rangle.
\]

Young's inequality absorbs the first term into the squared movement in (97.5). The result is

\[
\langle g_t,x_t-u\rangle
\le \frac{1}{2\eta}\left(
\|x_t-u\|_{H_t}^2-\|x_{t+1}-u\|_{H_t}^2
\right)
+\frac{\eta}{2}\|g_t\|_{H_t^{-1}}^2.
\tag{97.6}
\]

If \(H_t\) were fixed, the potential terms would telescope immediately. Here the metric grows over time, and the potential changes even when the point does not. Diagonal monotonicity provides the needed correction.

## 3. The AdaGrad regret bound

Assume every coordinate has bounded feasible diameter:

\[
|x_i-u_i|\le D_i
\qquad(x,u\in X).
\tag{97.7}
\]

Since \(h_{t,i}\) is nondecreasing in \(t\), a coordinatewise telescoping calculation gives

\[
\sum_{t=1}^T\left(
\|x_t-u\|_{H_t}^2-\|x_{t+1}-u\|_{H_t}^2
\right)
\le\sum_{i=1}^d D_i^2h_{T,i}.
\tag{97.8}
\]

To see the mechanism, fix one coordinate and write \(a_t=x_{t,i}-u_i\). Its sum is

\[
h_{1,i}a_1^2
+\sum_{t=2}^T(h_{t,i}-h_{t-1,i})a_t^2
-h_{T,i}a_{T+1}^2.
\]

The terminal term is nonpositive, while each remaining squared displacement is bounded by \(D_i^2\). The coefficient differences telescope to \(h_{T,i}\).

For the dual terms, let \(h_{0,i}=\delta\). The identity

\[
g_{t,i}^2=h_{t,i}^2-h_{t-1,i}^2
=(h_{t,i}-h_{t-1,i})(h_{t,i}+h_{t-1,i})
\]

implies \(g_{t,i}^2/h_{t,i}\le2(h_{t,i}-h_{t-1,i})\). Therefore

\[
\sum_{t=1}^T\|g_t\|_{H_t^{-1}}^2
=\sum_{i=1}^d\sum_{t=1}^T\frac{g_{t,i}^2}{h_{t,i}}
\le2\sum_{i=1}^d h_{T,i}.
\tag{97.9}
\]

Combine convexity, (97.6), (97.8), and (97.9). For every fixed comparator \(u\in X\) and every \(\eta>0\),

\[
\operatorname{Regret}_T(u)
=\sum_{t=1}^T(f_t(x_t)-f_t(u))
\le
\frac{1}{2\eta}\sum_{i=1}^dD_i^2h_{T,i}
+\eta\sum_{i=1}^dh_{T,i}.
\tag{97.10}
\]

This is a pathwise bound: it holds for every realized sequence of subgradients satisfying the stated geometry. If the horizon and a deterministic upper bound on the right-hand data are known in advance, \(\eta\) can be chosen accordingly. Minimizing the displayed expression after the sequence is observed gives the benchmark

\[
\operatorname{Regret}_T(u)
\le
\sqrt{2\left(\sum_iD_i^2h_{T,i}\right)
\left(\sum_i h_{T,i}\right)}.
\tag{97.11}
\]

This optimized expression is a bound on the best tuning parameter for that gradient history; it is not itself an online rule if it uses future gradients. Unknown-horizon or data-dependent tuning requires a separate schedule or doubling argument.

If \(T\) and coordinatewise bounds \(|g_{t,i}|\le G_i\) are known in advance, replace \(h_{T,i}\) by the deterministic upper bound \(\bar h_i=\sqrt{\delta^2+TG_i^2}\). For a non-singleton feasible set, choosing
\[
\eta=\sqrt{\frac{\sum_iD_i^2\bar h_i}{2\sum_i\bar h_i}}
\]
before the first round yields the valid regret bound \(\sqrt{2(\sum_iD_i^2\bar h_i)(\sum_i\bar h_i)}\). If \(X\) is a singleton, regret is identically zero. This tuning can be conservative, but it does not depend on future samples.

The stabilizer convention is part of the algorithm. Here \(\delta\) is added in quadrature before taking the square root, so \(h_{0,i}=\delta\) and \(h_{t,i}>0\). Implementations that add a small constant after the square root define a different sequence of metrics. Their update may be sensible, but the telescoping calculation must use the corresponding definition. Likewise, this chapter includes \(g_t\) in \(H_t\) because the metric is chosen after the round-\(t\) gradient is observed; an update using the previous accumulator has a different indexing convention.

The coordinate dependence is the main point. When gradients are concentrated on a few coordinates, only those coordinates accumulate large scales. A single Euclidean bound compresses the entire history into \(\sum_t\|g_t\|_2^2\); (97.10) retains the separate contribution of each coordinate and its feasible diameter.

This is not an unconditional dominance result. The geometry, the gradient sequence, and the coordinate diameters all matter. The useful conclusion is that the proof keeps enough information to distinguish these cases, while one global norm necessarily combines them.

## 4. Two examples

### 4.1 Sparse online features

Suppose \(X=[-1,1]^d\), so \(D_i=2\) for every coordinate. A linear prediction loss often produces a subgradient supported only on the nonzero features of the current example. If feature \(i\) appears on \(N_i\) rounds and \(|g_{t,i}|\le G_i\), then

\[
h_{T,i}\le\sqrt{\delta^2+N_iG_i^2}.
\]

The AdaGrad bound sums these coordinate scales rather than treating every feature as if it had been active on all \(T\) rounds. Rare features are not forced to use the small global step dictated by the most frequently active coordinate. The guarantee still depends on the feasible coordinate diameters; a rare feature with an enormous admissible range is not automatically cheap.

This example is also a formalization guide. The support condition can be stated as \(g_{t,i}=0\) outside a finite active set \(A_t\). The sum of squares for coordinate \(i\) then reduces to rounds for which \(i\in A_t\), but the theorem does not require a sparse representation. Sparsity is an optional lemma that sharpens its bound.

### 4.2 From online regret to stochastic risk

Let samples \(\xi_t\) be independent and identically distributed, and let \(f_t(x)=\ell(x;\xi_t)\) be convex. Assume \(x_t\) is chosen from earlier samples and \(g_t\in\partial_x\ell(x_t;\xi_t)\). If the same loss and subgradient bounds hold on every realized sample path, (97.10) is pathwise. Taking expectations and using freshness of \(\xi_t\) gives

\[
\mathbb E[\ell(x_t;\xi_t)]=\mathbb E[F(x_t)],
\qquad
\mathbb E[\ell(u;\xi_t)]=F(u),
\]

where \(F(x)=\mathbb E_\xi[\ell(x;\xi)]\). Convexity then gives an expected population-risk bound for the averaged iterate \(\bar x_T\), by the same online-to-batch argument as Chapter 94. Unlike Chapter 95's bounded-second-moment theorem, the AdaGrad route can keep coordinatewise gradient histories visible in the final guarantee.

If losses or gradients are unbounded, this expectation step needs integrability assumptions. If samples are dependent, freshness no longer gives the displayed identity without conditioning or a mixing argument. The pathwise regret theorem is therefore the algorithmic core; the stochastic interpretation is a separate corollary with its own hypotheses.

### 4.3 A one-coordinate versus all-coordinate history

Take \(X=[-R,R]^d\), so \(D_i=2R\). Suppose gradients are supported on coordinate \(j\), with \(|g_{t,j}|\le G\). Then \(h_{T,j}\le\sqrt{\delta^2+TG^2}\), while every other \(h_{T,i}=\delta\). The optimized bound (97.11) is proportional to

\[
R\left(\sqrt{\delta^2+TG^2}+(d-1)\delta\right).
\]

For a long horizon with fixed \(\delta\), its leading term is \(RG\sqrt T\), with no \(\sqrt d\) factor. A global Euclidean guarantee uses \(D_2=2R\sqrt d\) and \(\|g_t\|_2\le G\), producing a term proportional to \(RG\sqrt{dT}\).

If instead every coordinate receives a gradient of magnitude about \(G\) on every round, then \(h_{T,i}\) is about \(G\sqrt T\) for all \(i\). The diagonal bound scales like \(RdG\sqrt T\), the same dimension order as the Euclidean bound \(D_2\sqrt{\sum_t\|g_t\|_2^2}\). AdaGrad records the sequence's geometry; it does not promise a smaller rate for every sequence.

## 5. Diagonal and full-matrix geometry

The diagonal matrix \(H_t\) learns separate scales but does not represent correlations between coordinates. A full-matrix variant accumulates outer products \(g_sg_s^\mathsf T\) and uses a matrix square root in its proximal geometry. This can adapt to rotated low-dimensional structure, but storing and updating a dense matrix costs \(O(d^2)\) memory and substantially more computation. Diagonal AdaGrad sacrifices rotational sensitivity for coordinatewise efficiency.

This choice is a modeling decision, much like the mirror map in Chapter 94. A diagonal preconditioner is well suited when coordinates have direct meaning, features are sparse, and coordinatewise history is informative. A full matrix can help when the informative directions are combinations of coordinates, but its cost and matrix square-root proofs are much heavier. Neither geometry is uniformly best.

AdaGrad is also not a generic proof of convergence for every adaptive optimizer. Its guarantee relies on the nondecreasing cumulative metric and the corresponding proximal update. Methods that use moving averages, bias correction, or momentum have different state variables and require separate arguments.

## 6. Lean proof architecture

### 6.1 Represent the accumulator as finite data

For a gradient history \(g:\mathbb N\to\mathrm{Fin}(d)\to\mathbb R\), define the coordinate scale using a finite sum:

~~~lean
def adaScale {d : ℕ} (δ : ℝ)
    (g : ℕ → Fin d → ℝ) (t : ℕ) (i : Fin d) : ℝ :=
  Real.sqrt (δ ^ 2 + ∑ s ∈ Finset.range (t + 1), (g s i) ^ 2)
~~~

Prove positivity from \(\delta>0\) and monotonicity by extending the finite sum with one nonnegative square. Package these facts before defining the weighted norm. The metric's positive definiteness is what makes the proximal objective strictly convex and the inverse diagonal weights meaningful.
In the executable version below, `Finset.range t` represents the first `t` gradient observations using zero-based indexing. The stabilizer makes each scale positive, and appending one squared coordinate makes it monotone.

```lean
import Book.Models.FiniteOptimization

open Book.Models.FiniteOptimization

def accumulatedSquares : Nat := 3 * 3 + 4 * 4

theorem adagrad_accumulator_example : accumulatedSquares = 25 := by decide

theorem accumulator_is_nonnegative : 0 ≤ accumulatedSquares := by omega

noncomputable def adagradScale97 {d : Nat} (delta : ℝ)
    (g : Nat → Fin d → ℝ) (t : Nat) (i : Fin d) : ℝ :=
  Real.sqrt (delta ^ 2 + ∑ s ∈ Finset.range t, (g s i) ^ 2)

theorem adagradScale97_pos {d : Nat} (delta : ℝ)
    (g : Nat → Fin d → ℝ) (t : Nat) (i : Fin d) (hδ : 0 < delta) :
    0 < adagradScale97 delta g t i := by
  unfold adagradScale97
  apply Real.sqrt_pos.2
  have hsum : 0 ≤ ∑ s ∈ Finset.range t, (g s i) ^ 2 := by
    apply Finset.sum_nonneg
    intro s hs
    exact sq_nonneg _
  have hδsq : 0 < delta ^ 2 := sq_pos_of_pos hδ
  nlinarith

theorem adagradScale97_succ_mono {d : Nat} (delta : ℝ)
    (g : Nat → Fin d → ℝ) (t : Nat) (i : Fin d) :
    adagradScale97 delta g t i ≤ adagradScale97 delta g (t + 1) i := by
  unfold adagradScale97
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_range_succ]
  nlinarith [sq_nonneg (g t i)]
```

### 6.2 Separate the update certificate from metric growth

The weighted proximal update should provide a three-point certificate like (97.6) for each round and comparator. It depends on optimality in the \(H_t\)-metric but not on how \(H_t\) was generated. A separate accumulator lemma proves that the sequence of diagonal entries is nondecreasing. Finally, a coordinatewise telescope combines the changing potentials using the diameter bound (97.7).

This separation prevents one fragile lemma from simultaneously unfolding the argmin, simplifying square roots, proving coordinate monotonicity, and summing the horizon. It also exposes the reusable interface: any positive nondecreasing diagonal metric can use the same variable-potential telescope.

When proving (97.8), prefer a scalar telescope for each coordinate to a matrix identity about changing norms. The scalar proof exposes exactly which hypotheses are used: \(h_{t,i}-h_{t-1,i}\ge0\), the comparator displacement is bounded by \(D_i\), and the terminal square is nonnegative. The accumulator proof supplies the first fact, compactness or an explicit domain bound supplies the second, and order on \(\mathbb R\) supplies the third. No matrix square-root API is needed for the diagonal theorem.

### 6.3 Make the update timing explicit

The predictor \(x_t\) depends only on gradients observed through round \(t-1\). After \(g_t\) is revealed, form \(H_t\) including \(g_t\), then compute \(x_{t+1}\). In a formal state machine, store \(x_t\) and the accumulated coordinate squares before the round; update the accumulator and point in one transition. If the accumulator is updated before the prediction, the formal algorithm has a different information pattern.

For the stochastic corollary, keep measurability of \(x_t\), sample freshness, and the pathwise regret hypothesis separate from the weighted-metric theorem. This mirrors Chapters 95–96: deterministic algorithmic certificates first, probability wrappers afterward.

~~~text
finite gradient history
          |
          v
positive nondecreasing coordinate scales
          |
          v
weighted proximal certificate
          |
          v
coordinatewise potential telescope
          |
          v
pathwise regret, then optional expectation
~~~

This dependency diagram is also a useful development order. Each arrow should correspond to a lemma with a small interface, so the final theorem does not need to unfold how the adaptive scales were computed.

## 7. Common failure modes

1. **Using one scalar norm after introducing coordinate adaptation.** The proof must retain the diagonal entries through both primal and dual terms.
2. **Forgetting the initial stabilizer.** With \(\delta=0\), a coordinate with zero gradient history has a singular inverse metric.
3. **Assuming a changing metric telescopes unchanged.** The additional \(H_t-H_{t-1}\) terms are bounded using coordinate diameters.
4. **Using the accumulator before observing the gradient.** The update in (97.2) uses the current gradient to define its metric.
5. **Choosing a hindsight learning rate and calling it online.** The optimized bound (97.11) may depend on future gradient history.
6. **Claiming coordinatewise adaptation handles arbitrary rotations.** Diagonal metrics depend on the chosen coordinate system.
7. **Dropping the compactness or existence argument for the weighted projection.** A positive metric and a closed convex feasible set are needed; compactness is one simple sufficient condition.
8. **Converting regret to risk without fresh samples.** Adapted or dependent data need a conditional expectation argument.
9. **Applying the AdaGrad proof to Adam or momentum without changes.** Their moving state and update rule change the potential calculation.
10. **Mixing accumulator algebra with the mirror step.** Prove positivity, monotonicity, and the proximal certificate as separate lemmas.

## 8. Exercises

1. Prove the weighted three-point identity (97.5).
2. Derive (97.6) from the first-order condition (97.4) and Young's inequality.
3. Expand the coordinatewise sum and prove (97.8).
4. Prove \(g_{t,i}^2/h_{t,i}\le2(h_{t,i}-h_{t-1,i})\) and derive (97.9).
5. Combine convexity and the potential inequality to prove (97.10).
6. Optimize the right side of (97.10) over a fixed \(\eta>0\) and derive (97.11).
7. For sparse features, express \(h_{T,i}\) using the number of active rounds.
8. Prove the stochastic online-to-batch statement under independent samples and integrability.
9. Formalize the accumulator on \(\mathrm{Fin}(d)\) and prove positivity and monotonicity.
10. Define a weighted projection certificate and prove the one-round inequality without referring to a particular optimizer implementation.
11. Give an example where a diagonal metric helps and a rotated coordinate system changes the bound.
12. Explain which additional state would be needed to analyze a momentum-based adaptive method.

## 9. Chapter summary

Diagonal AdaGrad chooses a positive metric from the coordinatewise history of squared gradients. The weighted projection optimality condition yields a mirror-descent inequality. Although the metric changes each round, its coordinatewise monotonicity lets the potential telescope with a correction controlled by coordinate diameters. The resulting regret bound depends on the accumulated magnitude of each coordinate separately.

In Lean, represent the accumulator by finite sums, prove positivity and monotonicity first, and isolate the weighted proximal certificate from the variable-metric telescope. Treat online regret as the core theorem and derive stochastic risk guarantees only after adding sample-freshness and integrability hypotheses.

## Further reading

- Duchi, Hazan, and Singer, [“Adaptive Subgradient Methods for Online Learning and Stochastic Optimization”](https://www.jmlr.org/papers/v12/duchi11a.html), for diagonal and full-matrix AdaGrad and adaptive proximal geometries.
- [Chapter 94 — Mirror Descent and Bregman Geometry](chapter-94-mirror-descent-and-bregman-geometry.md), for the fixed-geometry regret proof generalized by the variable metric in this chapter.
- [Chapter 95 — Stochastic Gradient Methods and Expected Guarantees](chapter-95-stochastic-gradient-methods-and-expected-guarantees.md), for conditional stochastic-oracle bounds and online-to-batch conversion.
