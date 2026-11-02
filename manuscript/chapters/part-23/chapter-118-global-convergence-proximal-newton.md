# Chapter 118 — Global Convergence of Proximal Newton Iterations

> **Audience.** This chapter continues the inexact proximal Newton analysis of Chapter 117. It turns a one-step descent certificate into a global convergence theorem for accumulation points, and makes the compactness, metric, and line-search assumptions visible.

An Armijo inequality is a local statement about one accepted step. A convergence theorem is a statement about an entire sequence. Between the two lie several arguments: the objective decrease must be summable, the direction must become small, inner residuals must vanish in an ordinary norm, and a limit of subgradient witnesses must remain a valid subgradient witness.

These steps are familiar in numerical optimization, but they are exactly where formal proofs tend to skip hypotheses. We will prove a useful sufficient theorem for the method of Chapter 117. Its assumptions are intentionally explicit; they make each transition from algorithmic evidence to a limiting stationarity condition auditable.

## Learning objectives

After this chapter, you should be able to:

- derive a uniform lower bound on accepted backtracking step lengths;
- telescope Armijo decrease into a finite-energy estimate;
- use uniform spectral bounds to show that both directions and residuals vanish;
- pass subgradient witnesses to a cluster point using closedness of the convex subdifferential;
- distinguish stationary cluster points from convergence of the entire sequence;
- encode the finite-sum part of the proof as a reusable Lean lemma.

## 1. The convergence question

Let \(F=f+g\), where \(f:\mathbb R^n\to\mathbb R\) is continuously differentiable and \(g:\mathbb R^n\to\mathbb R\cup\{+\infty\}\) is proper, lower semicontinuous, and convex. At iteration \(k\), suppose the inner solver returns a displacement \(d_k\), a candidate \(y_k=x_k+d_k\), and a subgradient witness \(v_k\in\partial g(y_k)\). Define the model residual and composite slope by
\[
r_k=\nabla f(x_k)+H_kd_k+v_k,
\qquad
\Delta_k=\langle\nabla f(x_k),d_k\rangle+g(x_k+d_k)-g(x_k).
\tag{118.1}
\]
Here \(H_k\) is symmetric positive definite. Assume the relative certificate from Chapter 117:
\[
\|r_k\|_{H_k^{-1}}\le\eta_k\|d_k\|_{H_k},
\qquad 0\le\eta_k\le\bar\eta<1.
\tag{118.2}
\]
As shown there, the certificate implies
\[
\Delta_k\le-(1-\bar\eta)\|d_k\|_{H_k}^2.
\tag{118.3}
\]
For \(d_k\ne0\), this is a strict descent direction. Backtracking selects \(\alpha_k\in\{1,\rho,\rho^2,\ldots\}\), for some fixed \(\rho\in(0,1)\), and sets \(x_{k+1}=x_k+\alpha_kd_k\) with
\[
F(x_{k+1})\le F(x_k)+\sigma\alpha_k\Delta_k,
\qquad 0<\sigma<1.
\tag{118.4}
\]

The algorithmic certificate controls a proposed direction, and the line search controls the true objective after scaling that direction. The convergence proof needs both. It also needs uniform conditions; a positive-definite \(H_k\) at every individual iteration is weaker than a uniform lower eigenvalue bound across all iterations.

## 2. From a line search to a uniform step size

### 2.1 A sufficient Armijo threshold

Assume that \(\nabla f\) is \(L\)-Lipschitz on every trial segment \([x_k,x_k+d_k]\), for one constant \(L>0\). For \(0\le\alpha\le1\), the smooth descent lemma and convexity of \(g\) yield
\[
F(x_k+\alpha d_k)
\le F(x_k)+\alpha\Delta_k+\frac L2\alpha^2\|d_k\|^2.
\tag{118.5}
\]
The Armijo inequality is therefore guaranteed whenever
\[
\alpha\le\frac{2(1-\sigma)(-\Delta_k)}{L\|d_k\|^2}.
\tag{118.6}
\]
Unlike Chapter 117’s pointwise termination argument, global convergence needs one lower bound on the accepted \(\alpha_k\) that works for every iteration.

### 2.2 Uniform model bounds

Suppose there are constants \(0<\mu\le M<\infty\) such that
\[
\mu I\preceq H_k\preceq MI
\qquad\text{for every }k.
\tag{118.7}
\]
The lower bound gives \(\|d_k\|_{H_k}^2\ge\mu\|d_k\|^2\). Combining this with (118.3) shows that the threshold in (118.6) is at least
\[
c_\alpha:=\frac{2(1-\sigma)(1-\bar\eta)\mu}{L}>0.
\tag{118.8}
\]
Every \(\alpha\le\min\{1,c_\alpha\}\) therefore passes the Armijo test. If backtracking tests \(1,\rho,\rho^2,\ldots\), the first accepted length obeys
\[
\alpha_k\ge\underline\alpha:=\min\{1,\rho c_\alpha\}>0.
\tag{118.9}
\]
Indeed, when the threshold is below one, the preceding rejected grid point was larger than the threshold, so the accepted point is larger than \(\rho c_\alpha\). If the threshold is at least one, the full step is accepted. The uniform bound has four visible inputs: a strict forcing cap, a lower curvature bound, a smoothness bound, and the geometric backtracking factor.

The local Lipschitz assumption can be replaced by any uniform remainder bound that makes a fixed positive interval of step lengths acceptable. A globally Lipschitz gradient is sufficient. In local analyses, one can instead prove that all trial segments lie in a compact neighborhood on which the gradient has a common Lipschitz constant. A compact level set alone does not ensure this, because an unscaled model candidate may lie outside the level set.

## 3. Finite energy and vanishing directions

### 3.1 Telescoping the decrease

Combining Armijo decrease, the descent certificate, and the lower step bound gives
\[
F(x_{k+1})
\le F(x_k)-\sigma\underline\alpha(1-\bar\eta)\|d_k\|_{H_k}^2.
\tag{118.10}
\]
Let \(F_{\mathrm{low}}\) be a lower bound for \(F\) on the initial sublevel set. Summing (118.10) from \(k=0\) through \(N-1\) cancels the intermediate objective values:
\[
\sigma\underline\alpha(1-\bar\eta)
\sum_{k=0}^{N-1}\|d_k\|_{H_k}^2
\le F(x_0)-F_{\mathrm{low}}.
\tag{118.11}
\]
The right side is independent of \(N\). Since the terms in the sum are nonnegative, the infinite series is finite, so \(\|d_k\|_{H_k}\to0\). The lower bound in (118.7) then gives \(\|d_k\|\to0\).

This conclusion is stronger than saying that objective values converge. A bounded monotone sequence of objective values says nothing by itself about the distance between successive iterates. The decrease estimate charges each squared direction to a fixed finite budget; that is what forces the directions to vanish.

### 3.2 The role of compact level sets

If the initial sublevel set
\[
\mathcal L_0=\{x:F(x)\le F(x_0)\}
\tag{118.12}
\]
is compact, every iterate lies in \(\mathcal L_0\) by (118.4), so the sequence has at least one cluster point. Compactness does not prove stationarity; it only supplies convergent subsequences. Section 4 connects those subsequences to the inner residual and subgradient witness.

For a coercive objective on \(\mathbb R^n\), finite sublevel sets are bounded; lower semicontinuity makes them closed, hence compact. Other settings may use a separate invariant compact set. In an infinite-dimensional space, boundedness alone need not give a norm-convergent subsequence, so the compactness argument must be adapted to the topology in use.

## 4. Stationarity of every cluster point

### 4.1 The residual tends to zero

The upper spectral bound in (118.7) converts the dual-metric residual estimate into an ordinary Euclidean estimate:
\[
\|r_k\|
\le\sqrt M\,\|r_k\|_{H_k^{-1}}
\le\sqrt M\,\bar\eta\|d_k\|_{H_k}
\le M\bar\eta\|d_k\|.
\tag{118.13}
\]
Since \(d_k\to0\), we obtain \(r_k\to0\). The upper bound on \(H_k\) is essential here: it makes \(H_kd_k\to0\) and controls the conversion from the changing dual metric. The lower bound was used earlier to obtain a uniform step size and to infer Euclidean direction decay.

### 4.2 Passing the witness to the limit

Let \(x_{k_j}\to x^*\) be any convergent subsequence. Since \(d_k\to0\), the candidate points \(y_{k_j}=x_{k_j}+d_{k_j}\) also converge to \(x^*\). Rearranging (118.1) gives
\[
v_{k_j}=r_{k_j}-\nabla f(x_{k_j})-H_{k_j}d_{k_j}.
\tag{118.14}
\]
Continuity of \(\nabla f\), the residual limit, and the uniform bound on \(H_k\) show that \(v_{k_j}\to-\nabla f(x^*)\). Each witness lies in \(\partial g(y_{k_j})\). The graph of the subdifferential of a proper lower-semicontinuous convex function is closed, so taking limits yields
\[
-\nabla f(x^*)\in\partial g(x^*),
\qquad\text{equivalently}\qquad
0\in\nabla f(x^*)+\partial g(x^*).
\tag{118.15}
\]
This is the composite first-order stationarity condition. Notice the entire chain of witnesses: the solver returns \(v_k\), the residual equation controls that witness, and closedness preserves it at the limit. A proof that drops \(v_k\) and keeps only an informal “approximately solved” statement has no object to pass to the limit.

### 4.3 A sufficient global convergence theorem

We can now state the result in a form well suited to formalization.

**Theorem 118.1 (Cluster-point stationarity).** Suppose that every nonterminal iteration satisfies (118.1)–(118.4), that \(\nabla f\) has a common Lipschitz constant \(L>0\) on all trial segments, and that (118.7) holds. Suppose also that the initial sublevel set is compact and \(F\) is bounded below there. Then either an iteration has \(d_k=0\), in which case (118.2) implies that the current iterate is stationary, or the sequence has a cluster point. Every cluster point is stationary.

If \(f\) is convex as well as differentiable, every stationary point of \(f+g\) is a global minimizer. Without convexity of \(f\), the conclusion is stationarity only; local minima and saddle points are both possible. The theorem does not claim that the whole sequence converges to one point.

## 5. Cluster points versus whole-sequence convergence

The accepted displacement is \(x_{k+1}-x_k=\alpha_kd_k\), and \(0<\alpha_k\le1\). Thus \(\|x_{k+1}-x_k\|\to0\). For an infinite bounded sequence in finite-dimensional space, this asymptotic regularity implies that its set of cluster points is connected. The cluster set is also contained in the stationary set by Theorem 118.1.

If the initial sublevel set contains only finitely many stationary points, a connected subset of that finite set has one element. The sequence then has a unique cluster point and, being bounded, converges to it. A convenient sufficient condition is that all stationary points in the level set are isolated and there are only finitely many of them. Strong convexity near one cluster point is a common local route to uniqueness, but it is a further hypothesis, not a consequence of Armijo decrease.

### 5.1 Objective convergence is not iterate convergence

The statement \(F(x_k)\downarrow\ell\) only concerns scalar values. For example, a constant objective on a set allows a sequence to move among points of that set while its objective stays unchanged. Such a sequence need not converge. The finite-energy argument adds \(d_k\to0\), and compactness adds cluster points; a uniqueness or connectedness argument is still needed to establish convergence of the entire sequence.

## 6. Worked examples

### 6.1 Exact Newton on a strongly convex quadratic

Let \(F(x)=\tfrac12(x-b)^TQ(x-b)\), where \(Q\succ0\), and take \(g=0\), \(f=F\), and \(H_k=Q\). The exact model step is \(d_k=b-x_k\), so \(r_k=0\), \(\eta_k=0\), and the full trial point is \(b\). With \(\sigma=\tfrac14\), the full step passes Armijo: the objective drops from \(F(x_k)\) to zero, while the predicted composite slope is \(-2F(x_k)\). The sequence terminates at the unique minimizer in one iteration.

This example satisfies uniform spectral bounds with \(\mu=\lambda_{\min}(Q)\) and \(M=\lambda_{\max}(Q)\). The general theorem’s machinery is much more than this case needs, but its constants remain valid. It also illustrates why a global convergence theorem is usually a sufficient theorem rather than a sharp rate result.

### 6.2 A fixed inexactness ratio on a sparse scalar problem

Consider
\[
F(x)=\tfrac12(x-3)^2+|x|,
\qquad x_0=4.
\tag{118.16}
\]
The minimizer is \(x^*=2\). Choose \(H_k=1\), \(\eta=\tfrac12\), and for \(x_k\ge2\) let
\[
d_k=-\tfrac23(x_k-2),
\qquad y_k=x_k+d_k=2+\tfrac13(x_k-2).
\tag{118.17}
\]
The candidate remains positive, so choose \(v_k=1\in\partial |y_k|\). Since \(f'(x)=x-3\), the residual is \(r_k=f'(x_k)+d_k+v_k=\tfrac13(x_k-2)\). Therefore \(|r_k|=\tfrac12|d_k|\), exactly meeting the relative certificate. The composite slope is \(\Delta_k=(x_k-2)d_k=-\tfrac23(x_k-2)^2\).

The full step is accepted for \(\sigma=\tfrac14\): writing \(e_k=x_k-2\), the objective gap is \(F(x_k)-F(2)=\tfrac12e_k^2\), and \(e_{k+1}=\tfrac13e_k\). Hence the new gap is \(\tfrac1{9}\) of the previous gap, while Armijo asks only for a decrease of \(\tfrac16e_k^2\). Starting from \(x_0=4\), the first candidate is \(8/3\), and the iterates converge geometrically to \(2\). This example shows a fixed forcing cap can give global descent and, in a simple regular problem, a linear rate. The linear rate here comes from the explicit contraction, not from the global stationarity theorem alone.

## 7. Lean proof architecture

### 7.1 Separate the proof into interfaces

The global argument has four reusable boundaries:

1. **Direction certificate:** subgradient membership, residual equation, relative tolerance, and metric bounds.
2. **Line-search certificate:** accepted \(\alpha_k\), Armijo inequality, and a uniform lower bound.
3. **Finite-energy lemma:** one-step decrease and a lower objective bound imply a uniform finite-sum estimate.
4. **Limit theorem:** direction and residual limits combine with closedness of the subdifferential graph.

The data flow is:

~~~text
inner residual + metric bounds ──► direction decrease ──┐
                                                        ├─► finite energy ─► dₖ → 0
Armijo search + uniform α lower bound ─► objective drop ┘                   │
                                                                            ▼
subgradient witnesses + closed graph ◄── rₖ → 0 ◄── Hₖ bounded ────────────┘
~~~

The finite-sum argument does not need vector spaces or optimization types. It can be proved over real sequences and reused for many algorithms. The limit theorem then consumes the analytic facts in the form it needs.

### 7.2 A finite-sum telescope

The following Lean lemma captures the algebraic core. The function \(q_k\) stands for a nonnegative measure of step size, such as \(\|d_k\|_{H_k}^2\); the one-step estimate can absorb the positive Armijo and forcing constants into \(c\).

~~~lean
import Mathlib

theorem finite_energy_bound
    (F q : ℕ → ℝ) (c lower : ℝ)
    (h_lower : ∀ n, lower ≤ F n)
    (h_step : ∀ n, F (n + 1) ≤ F n - c * q n)
    (N : ℕ) :
    c * (∑ n ∈ Finset.range N, q n) ≤ F 0 - lower := by
  have htel : ∀ N, F N ≤ F 0 - c * (∑ n ∈ Finset.range N, q n) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        nlinarith [ih, h_step N]
  nlinarith [htel N, h_lower N]
~~~

The optimizer-specific theorem should establish h_step from (118.10). Do not put the entire matrix, subgradient, and line-search argument into this induction: doing so obscures the simple invariant and makes it harder to reuse the finite-energy result.

## 8. Common failure modes

1. **Using pointwise line-search termination as a uniform step bound.** Each search can terminate while accepted lengths still approach zero.
2. **Assuming positive definiteness without uniform constants.** The smallest eigenvalue may tend to zero, defeating the descent-to-direction estimate.
3. **Using only a lower spectral bound.** It controls the direction norm but not the residual conversion or \(H_kd_k\to0\).
4. **Concluding stationarity from \(d_k\to0\) alone.** The residual and subgradient witness are needed to recover the inclusion.
5. **Claiming a minimizer for nonconvex \(f\).** The limit statement is stationarity unless the full objective is convex or additional local assumptions apply.
6. **Claiming full-sequence convergence from cluster-point stationarity.** Multiple stationary cluster points may remain without a uniqueness argument.
7. **Using compactness before proving descent.** The iterates stay in the initial sublevel set only after accepted steps are shown to decrease \(F\).
8. **Forgetting finite termination cases.** A zero direction is already stationary under the relative residual certificate and should be handled before a line search divides by its norm.

## 9. Exercises

1. Derive (118.5) from the smooth descent lemma and convex interpolation of \(g\).
2. Prove the uniform lower bound (118.9), treating separately \(c_\alpha\ge1\) and \(c_\alpha<1\).
3. Starting with (118.10), derive the finite-sum estimate (118.11) by induction on \(N\).
4. Verify the two norm conversions in (118.13) from the spectral bounds in (118.7).
5. Prove that a zero direction satisfying (118.2) yields \(0\in\nabla f(x_k)+\partial g(x_k)\).
6. In the limit argument, identify the exact use of continuity of \(\nabla f\), boundedness of \(H_k\), and closedness of the subdifferential graph.
7. For the scalar sparse example, verify the residual, slope, first candidate, and objective-gap contraction.
8. Give an objective with multiple stationary points and explain why the theorem does not select which one is a cluster point.
9. State a condition under which every stationary cluster point is a global minimizer.
10. Refactor the Lean telescope so the step decrease is indexed by Finset.range; identify which assumptions are unnecessary for the algebraic lemma itself.
11. Explain why a uniform lower bound on \(\alpha_k\) is necessary for this particular finite-energy proof, and propose another argument that could replace it.
12. Extend the theorem to a metric space setting. State the compactness and graph-closedness properties that must replace their Euclidean counterparts.

## 10. Chapter summary

Global convergence follows from a chain of quantitative implications. Uniform positive curvature and a strict forcing cap give a uniform Armijo step length. Summable objective decrease then forces the model directions to zero. A uniform upper metric bound also forces residuals to zero; the residual equation makes the subgradient witnesses converge to the negative gradient at any cluster point. Closedness of the convex subdifferential graph yields stationarity.

Compactness supplies cluster points, not convergence of the full sequence. For that stronger conclusion, add a uniqueness condition such as a finite stationary set together with asymptotic regularity. Formalize the telescope separately from the analytic and topological lemmas so the reusable core remains small.

## Further reading

- Kanzow and Lechner, [“Globalized inexact proximal Newton-type methods for nonconvex composite functions”](https://link.springer.com/article/10.1007/s10589-020-00243-6), for a proximal Newton globalization with global stationarity of accumulation points and local convergence results.
- Lee, Sun, and Saunders, [“Proximal Newton-type methods for convex optimization”](https://papers.neurips.cc/paper/4740-proximal-newton-type-methods-for-convex-optimization.pdf), for global convergence under positive-definite model bounds in the convex composite setting.
- Chapter 117 establishes the inexact residual descent certificate; Chapters 114–116 develop line search, variable metrics, and proximal Newton models.
