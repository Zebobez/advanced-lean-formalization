# Chapter 96 — Control Variates and Finite-Sum Variance Reduction

> **Audience.** This chapter builds on stochastic gradient methods from Chapter 95 and assumes convexity, smoothness, and strong convexity. It develops two finite-sum methods, SVRG and SAGA, whose estimators remain unbiased while their variance shrinks as the iterates approach an optimum.

Plain stochastic gradient descent can be effective when an objective is a large average of component losses. Its obstacle in finite-sum problems is persistent sampling noise: even at the minimizer of the average, individual component gradients may be nonzero. Variance-reduced methods exploit extra structure in the finite sum to cancel this noise.

The central tool is a control variate. A familiar random quantity is subtracted and a known average is added back, preserving the mean while reducing variance. SVRG uses a snapshot and one full gradient per epoch. SAGA uses a table of past component gradients. SVRG becomes exact when the current point and snapshot are optimal; SAGA removes residual noise once its table matches the optimal component gradients.

## Learning objectives

After this chapter, you should be able to:

- derive the SVRG estimator and prove its conditional unbiasedness;
- establish a component-smoothness variance bound relative to the snapshot and optimum;
- prove an epoch contraction for strongly convex finite sums;
- explain how SAGA's gradient table gives another unbiased control variate;
- compare sample cost, memory cost, and proof invariants for SVRG and SAGA;
- formalize estimator algebra, variance bounds, and epoch-level expectation separately.

## 1. Finite sums and persistent noise

Consider

\[
F(x)=\frac1n\sum_{i=1}^n f_i(x),
\tag{96.1}
\]

where \(f_i:\mathbb R^d\to\mathbb R\) is convex and \(L\)-smooth. Assume \(F\) is \(\mu\)-strongly convex, with \(0<\mu\le L\), and has minimizer \(x^\star\). Thus \(\nabla F(x^\star)=0\). The condition number is \(\kappa=L/\mu\).

Full gradient descent costs \(n\) component-gradient evaluations per step:

\[
\nabla F(x)=\frac1n\sum_{i=1}^n\nabla f_i(x).
\]

Sampling \(i\) uniformly and using \(\nabla f_i(x)\) is unbiased, but its variance at \(x^\star\) is generally

\[
\frac1n\sum_{i=1}^n\|\nabla f_i(x^\star)\|^2,
\]

which can be positive even though the average gradient is zero. Chapter 95 showed how this noise can produce a nonzero error floor for a constant step size. Variance reduction uses the finite-sum structure to remove the residual component disagreement.

Write \(\Delta(x)=F(x)-F(x^\star)\). The goal is not merely to produce an unbiased estimator. It is to construct an estimator whose second moment can be bounded in terms of \(\Delta(x)\) and another quantity that also shrinks as the algorithm converges.

## 2. SVRG as a snapshot control variate

Fix a snapshot \(\tilde x\) and compute its full gradient \(\nabla F(\tilde x)\). For a uniformly sampled index \(i\), define

\[
v_i(x;\tilde x)
=\nabla f_i(x)-\nabla f_i(\tilde x)+\nabla F(\tilde x).
\tag{96.2}
\]

The first two terms are a difference evaluated on the same component. The final term restores the mean of the subtracted quantity.

### 2.1 Unbiasedness

Conditional on the current iterate and snapshot, uniform sampling gives

\[
\mathbb E_i[v_i(x;\tilde x)]
=\nabla F(x)-\nabla F(\tilde x)+\nabla F(\tilde x)
=\nabla F(x).
\tag{96.3}
\]

The estimator is exactly the full gradient when \(x=\tilde x\), and it is zero at \(x=\tilde x=x^\star\). The second fact is stronger than unbiasedness: the variance vanishes at the optimum when the snapshot is optimal.

In the generic control-variate pattern, start with a random vector \(X\) whose mean is wanted, choose a correlated vector \(C\) whose mean is known, and use \(X-C+\mathbb E[C]\). Its mean remains \(\mathbb E[X]\), while its variance is the variance of \(X-C\). The method helps when \(X\) and \(C\) move together, so their difference is less variable than \(X\) itself. In SVRG they are gradients of the same sampled component at two nearby points. Smoothness bounds that difference by \(L\|x-\tilde x\|\). The stronger objective-gap estimate (96.5) then relates the variance to convergence of the current iterate and snapshot.

The estimator can be written as a Lean definition independently of any smoothness assumptions:

~~~lean
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def svrgEstimator {n : ℕ} (grad : Fin n → E → E)
    (fullGrad : E → E) (x snapshot : E) (i : Fin n) : E :=
  grad i x - grad i snapshot + fullGrad snapshot
~~~

The unbiasedness lemma then uses only that fullGrad is the average of the component gradients. Smoothness enters later, in the variance estimate, and should not be included as a hypothesis of the algebraic identity.

### 2.2 The variance bound

For the standard bound, assume each \(f_i\) is convex and \(L\)-smooth and use an unconstrained minimizer \(x^\star\). The smooth convex gradient inequality says

\[
\|\nabla f_i(z)-\nabla f_i(x^\star)\|^2
\le 2L\bigl(f_i(z)-f_i(x^\star)
-\langle\nabla f_i(x^\star),z-x^\star\rangle\bigr).
\tag{96.4}
\]

Let \(a_i=\nabla f_i(x)-\nabla f_i(x^\star)\) and \(b_i=\nabla f_i(\tilde x)-\nabla f_i(x^\star)\). Since \(\mathbb E_i[b_i]=\nabla F(\tilde x)\), the estimator can be rewritten as

\[
v_i(x;\tilde x)=a_i-(b_i-\mathbb E_i[b_i]).
\]

Use \(\|a-b\|^2\le2\|a\|^2+2\|b\|^2\) and the fact that centering cannot increase the second moment. Averaging (96.4) over \(i\) cancels the linear terms because \(\nabla F(x^\star)=0\). It follows that

\[
\mathbb E_i\|v_i(x;\tilde x)\|^2
\le 4L\bigl(\Delta(x)+\Delta(\tilde x)\bigr).
\tag{96.5}
\]

The two gaps have distinct roles. \(\Delta(x)\) measures the current point's error; \(\Delta(\tilde x)\) is the cost of using a stale snapshot. If both points approach \(x^\star\), the estimator's second moment approaches zero. This is the mechanism behind linear convergence in the strongly convex setting.

## 3. Inner loops and an epoch contraction

At epoch \(s\), fix \(\tilde x_s\), compute \(\nabla F(\tilde x_s)\), and initialize \(x_0=\tilde x_s\). For \(k=0,\ldots,m-1\), sample \(i_k\) uniformly and update

\[
x_{k+1}=x_k-\eta v_{i_k}(x_k;\tilde x_s).
\tag{96.6}
\]

Rather than returning only the last inner iterate, choose \(J\) uniformly from \(\{0,\ldots,m-1\}\) and set \(\tilde x_{s+1}=x_J\). The random-output convention makes the epoch objective equal to the average of the inner objective values, which is exactly what the proof controls.

### 3.1 One inner-step inequality

For fixed \(x_k\), take expectation over the sampled component. Unbiasedness (96.3), strong convexity, and the variance bound (96.5) give

\[
\begin{aligned}
\mathbb E_i\|x_{k+1}-x^\star\|^2
&=\|x_k-x^\star\|^2
-2\eta\langle\nabla F(x_k),x_k-x^\star\rangle
+\eta^2\mathbb E_i\|v_{i_k}(x_k;\tilde x_s)\|^2\\
&\le \|x_k-x^\star\|^2
-2\eta\Delta(x_k)-\eta\mu\|x_k-x^\star\|^2\\
&\quad+4L\eta^2\bigl(\Delta(x_k)+\Delta(\tilde x_s)\bigr).
\end{aligned}
\]

If \(0<\eta<1/(2L)\), rearranging yields

\[
2\eta(1-2L\eta)\mathbb E_i[\Delta(x_k)]
\le \|x_k-x^\star\|^2-\mathbb E_i\|x_{k+1}-x^\star\|^2
+4L\eta^2\Delta(\tilde x_s).
\tag{96.7}
\]

This inequality reveals the control-variate proof pattern. The current gap is charged against the decrease in squared distance; the snapshot error remains as a per-step residual.

### 3.2 Average the inner loop

Sum (96.7) over \(k=0,\ldots,m-1\). The distances telescope. Strong convexity gives

\[
\|x_0-x^\star\|^2=\|\tilde x_s-x^\star\|^2
\le\frac{2}{\mu}\Delta(\tilde x_s).
\]

Dropping the nonnegative terminal distance and dividing by \(2\eta(1-2L\eta)m\) shows that the uniformly selected inner iterate satisfies

\[
\mathbb E[\Delta(\tilde x_{s+1})\mid\tilde x_s]
\le \alpha\,\Delta(\tilde x_s),
\tag{96.8}
\]

where

\[
\alpha=
\frac{1}{\mu\eta(1-2L\eta)m}
+\frac{2L\eta}{1-2L\eta}.
\tag{96.9}
\]

Whenever \(\alpha<1\), repeated conditioning gives

\[
\mathbb E[\Delta(\tilde x_S)]
\le\alpha^S\Delta(\tilde x_0).
\tag{96.10}
\]

For a simple explicit choice, take \(\eta=1/(8L)\) and \(m\ge64L/\mu\). Then \(1-2L\eta=3/4\); the second term in (96.9) is \(1/3\), and the first is at most \(1/6\). Thus \(\alpha\le1/2\): each epoch halves expected suboptimality. This deliberately conservative derivation favors a transparent Lean proof over the sharpest constants. More refined analyses choose better step-size and epoch-length constants.

An epoch costs \(n\) component-gradient evaluations for the full snapshot gradient and approximately \(2m\) for the inner differences. With \(m\) proportional to \(L/\mu\), the evaluation cost per constant-factor reduction is \(O(n+L/\mu)\). Plain gradient descent costs \(n\) evaluations per step; stochastic gradient descent uses fewer per step but can retain a noise floor. SVRG balances a periodic full pass with low-variance inner updates.

## 4. SAGA keeps a gradient table

SVRG discards each epoch's snapshot after its inner loop. SAGA instead stores one old gradient \(h_i\) for every component and their average \(\bar h=\frac1n\sum_i h_i\). At a current point \(x\), sample \(i\) uniformly and use

\[
v_i^{\mathrm{SAGA}}(x)
=\nabla f_i(x)-h_i+\bar h.
\tag{96.11}
\]

Conditional on the stored table, which is part of the past, this estimator is unbiased:

\[
\mathbb E_i[v_i^{\mathrm{SAGA}}(x)]
=\nabla F(x)-\frac1n\sum_i h_i+\bar h
=\nabla F(x).
\]

After forming the update, replace \(h_i\) by \(\nabla f_i(x)\) and update the table average. The algorithm needs one new component gradient per step and no full-gradient pass at the start of each epoch, but stores \(n\) gradient vectors. For a \(d\)-dimensional problem, the table uses \(O(nd)\) memory.

The proof state is correspondingly different. SVRG's control variate depends on a fixed snapshot and its full gradient; SAGA's depends on a changing table. A useful SAGA potential combines the distance to the optimum with a measure of the table's error. The gradient table is not implementation clutter: it is part of the mathematical state needed for the contraction proof. SAGA also admits proximal variants for certain nonsmooth regularizers, but those require an additional composite optimality argument.

## 5. Two worked examples

### 5.1 Quadratic components with different centers

Let \(f_i(x)=\tfrac12\|x-a_i\|^2\). Then \(F(x)=\tfrac12\|x-\bar a\|^2+\text{constant}\), where \(\bar a=\frac1n\sum_i a_i\), and \(x^\star=\bar a\). Ordinary stochastic gradient descent samples \(x-a_i\); even at \(x^\star\), the variance is \(\frac1n\sum_i\|a_i-\bar a\|^2\).

For SVRG, however,

\[
v_i(x;\tilde x)
=(x-a_i)-(\tilde x-a_i)+(\tilde x-\bar a)
=x-\bar a
=\nabla F(x).
\tag{96.12}
\]

The component-dependent center cancels exactly. In this example the control variate removes all sampling noise, not merely enough to obtain a bound.

For a concrete two-component instance, take raw gradients 2 and 4, baseline gradients 1 and 3, and snapshot gradient 2. The raw mean is 3 with variance 1. The SVRG correction is constantly 3, so it preserves the mean and reduces the variance to zero.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def rawGradientSample : State → Int := fun s => if s = zero then 2 else 4
def baselineGradientSample : State → Int := fun s => if s = zero then 1 else 3
def snapshotGradient : Int := 2
def correctedSample (s : State) : Int :=
  rawGradientSample s - baselineGradientSample s + snapshotGradient

theorem corrected_sample_is_constant : ∀ s, correctedSample s = 3 := by decide

theorem corrected_sample_preserves_mean :
    expectationNumerator uniformWeight correctedSample =
      expectationNumerator uniformWeight rawGradientSample := by decide

theorem raw_gradient_variance_numerator :
    expectationNumerator uniformWeight (fun s => (rawGradientSample s - 3) ^ 2) = 2 := by decide

theorem corrected_sample_variance_numerator :
    expectationNumerator uniformWeight (fun s => (correctedSample s - 3) ^ 2) = 0 := by decide
```

### 5.2 Regularized empirical risk

Suppose \(\ell_i(w)\) is a convex smooth loss on example \(i\), and define component functions

\[
f_i(w)=\ell_i(w)+\frac{\lambda}{2}\|w\|^2,\qquad \lambda>0.
\]

Then \(F=\frac1n\sum_i\ell_i+\frac{\lambda}{2}\|w\|^2\) is strongly convex when the losses are convex. SVRG computes \(\nabla F(\tilde w)\) once per epoch and samples differences of regularized component gradients. The regularization appears in both terms of each difference and is therefore handled consistently. If computing a full pass is costly but the data set fits in memory, the snapshot method trades that pass for low-variance updates. If memory is available for all \(n\) gradients and avoiding epoch boundaries matters, SAGA is a natural alternative.

## 6. Lean proof architecture

### 6.1 Prove the estimator identities first

Represent component gradients as a function indexed by Fin n, and represent the full gradient as their finite average. The SVRG unbiasedness proof is a finite-sum identity; it needs no smoothness, convexity, or strong convexity. The SAGA unbiasedness proof is also algebraic once the stored table is fixed. Proving these identities first isolates the control-variate design from the convergence analysis.

Require \(n>0\) when defining a uniform average or selecting an index uniformly. This is easy to overlook in Lean because Fin 0 is an empty type, for which there is no uniform probability distribution.

### 6.2 State the smoothness lemma in the useful orientation

The variance proof needs the inequality (96.4) with the optimum in the second argument. A generic theorem about gradient Lipschitzness may not directly have this orientation. Establish a local lemma that combines convexity and smoothness into a bound on squared gradient differences by a function-value Bregman remainder. Then average over the component index; the linear terms cancel only after the finite sum is simplified to \(\nabla F(x^\star)=0\).

Do not silently assume every component gradient vanishes at the optimum. The proof uses cancellation of their average and controls their separate magnitudes by component function gaps.

### 6.3 Preserve the epoch snapshot in the induction motive

For the SVRG inner loop, the snapshot and its full gradient remain fixed while \(x_k\) changes. A useful invariant records:

- the current inner point is feasible (in an unconstrained theorem, this is automatic);
- the snapshot objective gap is fixed throughout the inner loop;
- the expected distance and objective gap satisfy the one-step inequality;
- the output index is uniform over the inner predictions.

At the epoch boundary, the random output becomes the next snapshot, so the invariant restarts with a new conditional expectation. This is a nested induction: an inner finite sum proves the epoch contraction, and an outer induction proves (96.10).

### 6.4 Model SAGA's table as algorithmic state

A SAGA state contains \(x\), a function Fin n → E storing the old gradients, and the average of that table. Updating one entry should be expressed as a local table update, with a lemma that the cached average changes by \((g_{\mathrm{new}}-g_{\mathrm{old}})/n\). Prove the estimator's conditional mean using the pre-update table. Updating the table before proving unbiasedness changes the random variable and is a common source of off-by-one errors.

The Lyapunov function should be introduced only after the table update is stable. It combines the objective gap or distance of \(x\) with a sum of table errors. This enlarged potential is the proof certificate for SAGA's memory-bearing state.

## 7. Common failure modes

1. **Subtracting a component gradient without adding its mean back.** That changes the expected direction.
2. **Using a different sample index in the two gradient terms.** The shared index is what makes the difference a useful control variate.
3. **Assuming component gradients vanish at \(x^\star\).** Only their average is zero in general.
4. **Claiming zero variance everywhere.** SVRG has zero variance at the snapshot and at an optimal snapshot; away from these points use (96.5).
5. **Returning the last inner iterate while citing an average-output theorem.** The proof of (96.8) uses a uniform random inner iterate.
6. **Forgetting the full-gradient cost.** Snapshot computation requires a complete pass through the finite sum.
7. **Omitting the snapshot error from the variance bound.** A stale reference contributes the second gap in (96.5).
8. **Treating the SAGA table as a constant.** It is updated after every sample and belongs in the induction state.
9. **Confusing an expected epoch contraction with pathwise contraction.** Equations (96.8)–(96.10) are in expectation.
10. **Using a sharp paper theorem with mismatched output conventions.** Match assumptions, step size, epoch length, and random-output rule exactly.

## 8. Exercises

1. Prove the SVRG unbiasedness identity (96.3).
2. Derive the variance bound (96.5) from (96.4), including the cancellation of the linear terms.
3. Starting with the squared-distance expansion, prove (96.7).
4. Sum (96.7) and derive the contraction factor (96.9).
5. Verify that \(\eta=1/(8L)\) and \(m\ge64L/\mu\) imply \(\alpha\le1/2\).
6. Explain why a uniformly selected inner iterate gives the average objective in (96.8).
7. Prove the SAGA estimator (96.11) is conditionally unbiased given its table.
8. Work out the quadratic cancellation in (96.12) for scalar \(x\) and \(a_i\).
9. Count gradient evaluations and storage for one SVRG and one SAGA epoch.
10. Define the SVRG estimator in Lean and prove its finite-average identity before introducing smoothness assumptions.
11. Formalize a finite-sum Bregman-gradient bound that cancels the component linear terms.
12. Propose a Lyapunov structure for a SAGA state and identify the table-error quantity it must control.

## 9. Chapter summary

Finite-sum variance reduction uses the structure of \(F=\frac1n\sum_i f_i\) to cancel component-gradient noise. SVRG subtracts and restores a snapshot gradient, yielding an unbiased estimator whose second moment is bounded by the current and snapshot objective gaps. A random inner output converts a telescoping distance argument into an epoch contraction.

SAGA instead stores one past gradient per component. The stored table provides the control variate and becomes part of the proof state. SVRG spends a full pass at each epoch boundary and little memory; SAGA spends \(O(nd)\) memory and one new component gradient per update. In Lean, keep estimator algebra, smoothness bounds, inner-loop telescoping, and epoch-level induction in separate layers.

## Further reading

- Johnson and Zhang, [“Accelerating Stochastic Gradient Descent using Predictive Variance Reduction”](https://proceedings.neurips.cc/paper/2013/hash/ac1dd209cbcc5e5d1c6e28598e8cbbe8-Abstract.html), for SVRG and its finite-sum convergence analysis.
- Defazio, Bach, and Lacoste-Julien, [“SAGA: A Fast Incremental Gradient Method With Support for Non-Strongly Convex Composite Objectives”](https://proceedings.neurips.cc/paper_files/paper/2014/hash/937964195d6fb3a55cd7cc578165f058-Abstract.html), for the gradient-table method and its proximal extension.
- [Chapter 95 — Stochastic Gradient Methods and Expected Guarantees](chapter-95-stochastic-gradient-methods-and-expected-guarantees.md), for the stochastic-oracle and noise-floor analysis that motivates variance reduction.
