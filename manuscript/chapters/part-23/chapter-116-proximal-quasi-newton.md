# Chapter 116 — Proximal Quasi-Newton Methods and Structured Metrics

> **Audience.** This chapter builds on variable-metric forward–backward splitting from Chapter 115. It replaces a generic preconditioner with curvature models such as Hessians and quasi-Newton matrices, then studies the model subproblem, composite line search, and structured metrics that keep the proximal calculation practical.

Proximal gradient uses a scalar quadratic to approximate the smooth loss. A variable-metric method replaces that scalar with a positive-definite matrix. A proximal Newton method chooses the matrix from the Hessian; a proximal quasi-Newton method builds an approximation from gradient differences. Both retain the nonsmooth term exactly in the local model.

The matrix alone does not make an algorithm. The subproblem must provide a descent certificate, the line search must convert model decrease into true objective decrease, and the matrix structure must make the proximal calculation affordable. These pieces are especially suitable for formalization because each has a precise mathematical witness.

## Learning objectives

After this chapter, you should be able to:

- formulate a composite quadratic model and its proximal Newton direction;
- derive a strict composite descent certificate from positive definiteness;
- prove termination of an Armijo line search along that direction;
- distinguish globalized descent from local superlinear or quadratic convergence;
- reduce a diagonal-plus-low-rank metric proximal problem to a lower-dimensional dual equation;
- represent exact or inexact subproblem solutions with Lean certificates.

## 1. The composite quadratic model

### 1.1 Keep the nonsmooth term exact

Consider
\[
\min_{x\in\mathbb R^n}F(x):=f(x)+g(x),
\tag{116.1}
\]
where \(f\) is convex and twice differentiable and \(g\) is proper, closed, and convex. At the current point \(x\), choose a symmetric positive-definite matrix \(H\) and define
\[
m_H(y;x)
=f(x)+\langle\nabla f(x),y-x\rangle
+\frac12\langle H(y-x),y-x\rangle+g(y).
\tag{116.2}
\]
The smooth part is replaced by a quadratic approximation; the nonsmooth term remains unchanged. If \(H=\nabla^2 f(x)\), this is the proximal Newton model. If \(H\) is a positive-definite quasi-Newton approximation, it gives a proximal quasi-Newton model.

The model has a unique minimizer \(y\), since the quadratic term is strongly convex and \(g\) is convex. Write \(d=y-x\). Completing the square gives
\[
y=\operatorname{prox}^{H}_{g}
\bigl(x-H^{-1}\nabla f(x)\bigr),
\qquad
\operatorname{prox}^{H}_{g}(z)
=\arg\min_u\left(g(u)+\tfrac12\|u-z\|_H^2\right).
\tag{116.3}
\]
The matrix controls both the direction and the geometry of the proximal operation. When \(H=L I\), (116.3) reduces to an ordinary proximal-gradient step with scale \(1/L\). For general \(H\), the proximal map may be substantially harder.

### 1.2 The model yields a composite descent direction

Since \(y\) minimizes \(m_H(\cdot;x)\), compare it with \(x\):
\[
\langle\nabla f(x),d\rangle
+g(x+d)-g(x)
\le-\frac12\|d\|_H^2,
\qquad
\|d\|_H^2:=\langle Hd,d\rangle.
\tag{116.4}
\]
Define the model slope
\[
\Delta:=\langle\nabla f(x),d\rangle+g(x+d)-g(x).
\tag{116.5}
\]
If \(d\ne0\), positive definiteness makes \(\Delta<0\). If \(d=0\), the subproblem optimality condition is \(0\in\nabla f(x)+\partial g(x)\), the composite first-order condition. In the convex setting this certifies global optimality.

This is the key reason to solve a proximal model rather than apply an arbitrary Hessian direction to \(f\) and ignore \(g\). The nonsmooth term participates in the direction and in its descent certificate.

### 1.3 Updating a quasi-Newton metric

In a quasi-Newton method, the matrix is updated from observed curvature rather than recomputed as a full Hessian. Let \(s=x_{k+1}-x_k\) and \(q=\nabla f(x_{k+1})-\nabla f(x_k)\). The BFGS Hessian update is
\[
H_{k+1}
=H_k-\frac{H_kss^\mathsf TH_k}{s^\mathsf TH_ks}
+\frac{qq^\mathsf T}{s^\mathsf Tq}.
\]
It satisfies the secant equation \(H_{k+1}s=q\). If \(H_k\) is positive definite and \(s^\mathsf Tq>0\), the update remains positive definite. For a convex differentiable \(f\), gradient monotonicity gives \(s^\mathsf Tq\ge0\); a zero or numerically unreliable curvature pair must be skipped, damped, or regularized rather than fed blindly into the formula.

Limited-memory variants retain only a small number of pairs \((s,q)\), reducing storage and matrix-vector cost. The resulting metric is attractive only if its structured form also permits an efficient metric proximal step. Curvature quality and proximal cost are coupled design choices.

## 2. Globalizing the step

### 2.1 Armijo search on the composite objective

The full model step need not decrease the true objective if \(H\) is only an approximation to the local curvature. Choose \(\sigma\in(0,1)\) and a contraction \(\rho\in(0,1)\), and test \(\alpha=1,\rho,\rho^2,\ldots\) until
\[
F(x+\alpha d)\le F(x)+\sigma\alpha\Delta.
\tag{116.6}
\]
The accepted iterate is \(x^+=x+\alpha d\). The right side is strictly below \(F(x)\) when \(d\ne0\), so each accepted step has a quantitative objective decrease.

    current point x
          |
          +--> build H and solve the composite quadratic model
                         |
                         +--> direction d and negative model slope Δ
                                      |
                                      +--> Armijo tests F(x + α d)
                                                   |
                                                   +--> accepted step x⁺

Why does the search terminate? Convexity of \(g\) gives
\[
g(x+\alpha d)\le(1-\alpha)g(x)+\alpha g(x+d)
\quad(0\le\alpha\le1).
\tag{116.7}
\]
If \(\nabla f\) is locally Lipschitz near \(x\), then for some local constant \(L_x\),
\[
f(x+\alpha d)\le f(x)+\alpha\langle\nabla f(x),d\rangle
+\frac{L_x}{2}\alpha^2\|d\|^2.
\tag{116.8}
\]
Combining the two bounds yields \(F(x+\alpha d)\le F(x)+\alpha\Delta+O(\alpha^2)\). Since \(\Delta<0\) and \(\sigma<1\), all sufficiently small positive \(\alpha\) pass (116.6). Geometric backtracking therefore terminates.

Unlike Chapter 114's backtracking test, which enlarges a quadratic smoothness estimate and recomputes a proximal point, this search keeps the direction fixed and shrinks its length. The two line searches certify different objects and should be formalized with different predicates.

The Armijo test evaluates the true composite objective, not just its smooth part or its local model. If \(g\) is an indicator of a convex feasible set, both endpoints are feasible and the segment remains feasible. If \(g\) is an \(\ell_1\) penalty, convexity supplies the same segment inequality. The line search therefore handles constraints and regularizers through one certificate.

The local estimate makes the finite-termination argument quantitative. If \(L_x>0\) is valid in (116.8), any positive \(\alpha\le1\) satisfying
\[
\alpha\le\frac{2(1-\sigma)(-\Delta)}{L_x\|d\|^2}
\]
passes the Armijo test. Geometric backtracking eventually drops below this threshold. The bound depends on the direction and the current point; it is not a global lower bound on all future step lengths. This is sufficient for acceptance, but by itself it does not prove a global complexity bound.

### 2.2 What the global guarantee does and does not say

The exact subproblem and Armijo search prove monotone decrease and finite acceptance at every nonstationary point under local smoothness. A global convergence theorem additionally needs assumptions that prevent iterates from escaping and ensure the model matrices remain positive and well-scaled. Typical analyses assume bounded level sets and uniform spectral bounds on \(H_k\).

Local fast rates require more. With an exact Hessian model, a locally Lipschitz Hessian and suitable strong convexity yield quadratic convergence once full steps are accepted. A quasi-Newton sequence can yield superlinear convergence when its curvature errors satisfy a Dennis–Moré-type condition. These are local conclusions; they do not follow from Armijo decrease by itself.

Global analyses therefore state their safeguards explicitly: the level set containing the iterates should be bounded, and the model matrices should remain uniformly positive definite with controlled upper bounds. If a Hessian approximation loses positive definiteness, a common repair is damping, replacing it by \(H_k+\mu_k I\) or modifying its eigenvalues. This restores a descent model, but the damping schedule becomes part of the algorithm and of the proof. A convergent line search cannot compensate for a subproblem matrix that is singular or indefinite.

An inexact subproblem can be handled by retaining a residual. If an approximate direction \(d\) has
\[
r\in\nabla f(x)+Hd+\partial g(x+d),
\tag{116.9}
\]
then the subgradient inequality gives
\[
\Delta\le-\|d\|_H^2+\langle r,d\rangle.
\tag{116.10}
\]
Thus a relative residual bound \(\|r\|_{H^{-1}}\le(1-\theta)\|d\|_H\), with \(0<\theta<1\), implies \(\Delta\le-\theta\|d\|_H^2\). This is an explicit certificate that an iterative inner solver has made the model direction sufficiently accurate for descent.

## 3. Structured metric proximal calculations

### 3.1 Diagonal plus low rank

Suppose the metric matrix has the form
\[
H=D+VV^\mathsf T,
\tag{116.11}
\]
where \(D\) is positive diagonal and \(V\in\mathbb R^{n\times r}\) with \(r\ll n\). Directly applying a generic dense proximal solver can cost as much as solving a new high-dimensional problem. Instead, dualize only the low-rank quadratic.

For a metric proximal point \(x^\star=\operatorname{prox}^{H}_g(z)\), introduce \(q=V^\mathsf T(x^\star-z)\). The rank-\(r\) term admits the identity
\[
\frac12\|V^\mathsf T(x-z)\|^2
=\sup_{q\in\mathbb R^r}
\left\{\langle q,V^\mathsf T(x-z)\rangle-\frac12\|q\|^2\right\}.
\tag{116.12}
\]
For fixed \(q\), minimizing over \(x\) gives a diagonal-metric proximal map. At the optimum the dual and primal variables satisfy
\[
x(q)=\operatorname{prox}^{D}_{g}(z-D^{-1}Vq),
\qquad
q=V^\mathsf T(x(q)-z).
\tag{116.13}
\]
The original \(n\)-dimensional subproblem is therefore represented through an \(r\)-dimensional equation, provided the diagonal-metric proximal map is cheap. The strong convexity of the primal quadratic makes the primal solution unique; a dual derivation must still establish the existence and correct optimality relation for \(q\).

### 3.2 A two-coordinate example

Let \(g(x)=\lambda(|x_1|+|x_2|)\), \(D=I\), \(V=(1,1)^\mathsf T\), \(z=(2,0)\), and \(\lambda=\tfrac12\). Then \(H=I+VV^\mathsf T\), and (116.13) becomes
\[
x(q)=\bigl(\operatorname{soft}_{1/2}(2-q),
\operatorname{soft}_{1/2}(-q)\bigr),
\qquad
q=x_1(q)+x_2(q)-2.
\tag{116.14}
\]
The scalar value \(q=-\tfrac14\) satisfies the equation: \(x(q)=(\tfrac74,0)\), and \(\tfrac74+0-2=-\tfrac14\). Hence the metric proximal point is \((\tfrac74,0)\).

The Euclidean proximal point would be \((\tfrac32,0)\). The low-rank coupling shifts the solution because the metric penalizes the sum of the coordinate displacements in addition to their separate squared lengths. This example is small enough to verify by hand and illustrates why a generic separable soft-thresholding formula cannot be reused unchanged in a coupled metric.

The Lean development below verifies the scalar dual equation and proves the resulting point is a global minimizer of the coupled metric proximal objective. The comparison with the Euclidean soft-threshold point is also computed exactly.

```lean
def softThreshold116 (z threshold : ℚ) : ℚ :=
  if z < 0 then -max (-z - threshold) 0 else max (z - threshold) 0

def lowRankPrimal116 (q : ℚ) : ℚ × ℚ :=
  (softThreshold116 (2 - q) (1 / 2), softThreshold116 (-q) (1 / 2))

def lowRankDualMap116 (q : ℚ) : ℚ :=
  (lowRankPrimal116 q).1 + (lowRankPrimal116 q).2 - 2

def lowRankCandidate116 : ℚ × ℚ := ((7 : ℚ) / 4, 0)

theorem dual_variable_solves_low_rank_equation :
    lowRankDualMap116 (-(1 : ℚ) / 4) = -(1 : ℚ) / 4 := by
  norm_num [lowRankDualMap116, lowRankPrimal116, softThreshold116]

theorem low_rank_primal_point :
    lowRankPrimal116 (-(1 : ℚ) / 4) = lowRankCandidate116 := by
  norm_num [lowRankPrimal116, lowRankCandidate116, softThreshold116]

theorem euclidean_proximal_point_is_different :
    (softThreshold116 2 (1 / 2), softThreshold116 0 (1 / 2)) =
      ((3 : ℚ) / 2, 0) := by
  norm_num [softThreshold116]

def lowRankMetricObjective116 (x : ℚ × ℚ) : ℚ :=
  ((x.1 - 2) ^ 2 + x.2 ^ 2 + (x.1 + x.2 - 2) ^ 2) / 2 +
    (|x.1| + |x.2|) / 2

theorem low_rank_point_is_global_metric_proximum (x : ℚ × ℚ) :
    lowRankMetricObjective116 lowRankCandidate116 ≤
      lowRankMetricObjective116 x := by
  have hFirst : 0 ≤ |x.1| - (7 : ℚ) / 4 - (x.1 - 7 / 4) := by
    have h := le_abs_self x.1
    linarith
  have hSecond : 0 ≤ |x.2| - x.2 / 2 := by
    by_cases hx : 0 ≤ x.2
    · rw [abs_of_nonneg hx]
      nlinarith
    · have hx' : x.2 ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx']
      nlinarith
  norm_num [lowRankMetricObjective116, lowRankCandidate116]
  nlinarith [hFirst, hSecond, sq_nonneg (x.1 - 7 / 4),
    sq_nonneg x.2, sq_nonneg (x.1 + x.2 - 7 / 4)]
```

### 3.3 An exact scalar proximal Newton step

Let \(f(x)=\tfrac12a(x-b)^2\) and \(g(x)=\lambda|x|\), with \(a>0\). The Hessian model is exact, so its metric is \(H=a\), and the proximal Newton candidate is
\[
y=\operatorname{soft}_{\lambda/a}(b).
\]
For \(a=4\), \(b=3\), and \(\lambda=2\), this gives \(y=2.5\), the exact minimizer of \(2(x-3)^2+2|x|\). Starting from \(x^0=0\), the full model step reaches it in one iteration; with Armijo parameter \(\sigma=\tfrac14\), the step \(\alpha=1\) is accepted. This contrast with gradient descent is the benefit of a good curvature model; for a nonquadratic loss, the same full step may need to be shortened.

### 3.4 Logistic loss with an \(\ell_1\) penalty

For binary logistic regression, a typical objective is
\[
F(w)=\sum_{i=1}^m\log\bigl(1+\exp(-y_i a_i^\mathsf Tw)\bigr)
+\lambda\|w\|_1.
\tag{116.15}
\]
The smooth Hessian is \(A^\mathsf T W(w)A\), where \(W(w)\) is diagonal and positive semidefinite. A damped proximal Newton model can use \(H=A^\mathsf T W(w)A+\mu I\) with \(\mu>0\). Its subproblem is a weighted \(\ell_1\) problem, generally coupled across coordinates; coordinate descent or a structured low-rank/diagonal solver can produce an approximate direction and residual certificate.

The outer Armijo search evaluates the original logistic objective plus penalty. The inner solver only needs to decrease the quadratic model enough to certify a direction. Separating these tasks keeps the proof independent of the particular inner algorithm.

## 4. Lean proof architecture

### 4.1 Bundle the model certificate

Represent \(H\) as a symmetric positive-definite linear map and define the model objective separately. An exact direction certificate should contain:

1. the candidate point \(y=x+d\);
2. the subgradient witness \(v\in\partial g(y)\);
3. the optimality equation \(\nabla f(x)+Hd+v=0\);
4. positive definiteness of \(H\).

From these fields, prove uniqueness of the model minimizer and derive (116.4). This keeps the descent argument algebraic and avoids expanding a specific proximal implementation.

### 4.2 Make globalization evidence explicit

An accepted line-search step should retain \(\alpha>0\), the direction \(d\), the model slope \(\Delta\), and the Armijo inequality (116.6). The termination theorem consumes local smoothness, convexity of \(g\), and strict negativity of \(\Delta\). The objective-decrease theorem only consumes the accepted certificate.

For an inexact solve, keep the residual \(r\) from (116.9) and its norm bound. Do not hide inner-solver accuracy behind a bare statement that the candidate is “close.” The relative residual inequality gives exactly the negative slope needed by the line search.

Some inner methods provide a model-value gap more naturally than a subgradient residual. If an approximate point \(\tilde y=x+\tilde d\) satisfies \(m_H(\tilde y;x)\le m_H(x;x)-c\|\tilde d\|_H^2\) for a fixed \(c>0\), then its composite model slope is at most \(-(c+\tfrac12)\|\tilde d\|_H^2\). This is another valid interface for the globalization proof. Coordinate descent solvers may expose such a gap through a primal-dual certificate; an inner iteration count alone does not provide it.

For local superlinear convergence, the forcing tolerance generally must become stricter as the outer error shrinks. A fixed relative residual fraction can guarantee a uniformly negative direction while still leaving a first-order error in the local solve. Thus keep separate fields for the global descent tolerance and the stronger asymptotic accuracy condition.

### 4.3 Formalize the low-rank reduction compositionally

For (116.11)–(116.13), separate the base diagonal proximal map, the rank-\(r\) dual variable, and the equation connecting them. Prove that any pair satisfying (116.13) satisfies the optimality condition of the full metric subproblem; then use strong convexity for uniqueness. The converse direction establishes that the primal minimizer induces a dual witness.

In Lean, dimensions are the main bookkeeping risk: \(V\) maps \(\mathbb R^r\) to \(\mathbb R^n\), while \(V^\mathsf T\) maps back. State these maps with bundled linear maps or explicit finite indices, and prove the adjoint identity once. This prevents repeated coercion and transpose goals from obscuring the convex analysis.

## 5. Common failure modes

1. **Using a nonsymmetric or indefinite matrix.** The model may fail to be convex, so its minimizer and descent certificate are no longer guaranteed.
2. **Applying the ordinary prox to a dense metric.** The result solves a different subproblem unless the metric is a scalar multiple of the identity or a proven transformation applies.
3. **Ignoring \(g\) in the direction test.** The smooth gradient alone need not be a descent direction for the composite objective.
4. **Claiming a full Newton step is globally safe.** The model is local; use a line search or prove a majorization condition.
5. **Claiming quadratic convergence from SPD matrices.** Local fast rates require Hessian regularity and an accurate model, not just positive definiteness.
6. **Using an inexact direction without a residual bound.** A solver stopping flag is not a mathematical descent certificate.
7. **Forgetting the sign in the low-rank dual equation.** The metric proximal shift is \(z-D^{-1}Vq\), and the coupling condition is \(q=V^\mathsf T(x-z)\).
8. **Calling an \(r\)-dimensional dual solve free.** It can still be expensive if \(r\) is large or each evaluation of the base proximal map is costly.

## 6. Exercises

1. Derive (116.3) by completing the square in the quadratic model.
2. Prove (116.4) by comparing the model value at \(x+d\) and at \(x\).
3. Use (116.7)–(116.8) to show that Armijo backtracking terminates whenever \(d\ne0\).
4. Derive (116.10) from the residual inclusion and convexity of \(g\).
5. Verify the scalar dual solution in (116.14) and compare its value with the Euclidean proximal point.
6. Derive the low-rank dual relation (116.13) from the quadratic conjugate identity (116.12).
7. Explain which hypotheses are needed to upgrade monotone decrease to global convergence.
8. Give a logistic-regression instance where the Hessian is singular, and explain why damping is needed for a positive-definite model.
9. Design a Lean structure for an exact proximal Newton direction and list the fields needed for the Armijo proof.
10. State a plausible relative residual rule for an inexact inner solver and show how it implies strict model descent.

## 7. Chapter summary

Proximal Newton and quasi-Newton methods minimize a local quadratic model of the smooth loss while retaining the nonsmooth penalty exactly. Positive definiteness yields a composite descent certificate, and an Armijo line search turns that model decrease into true objective decrease. Structured diagonal-plus-low-rank metrics can make the otherwise coupled proximal subproblem tractable through a lower-dimensional dual equation.

In Lean, keep the model minimizer, descent slope, line-search acceptance, inexact residual, and structured metric calculation as separate certificates. This makes global decrease reusable across different subproblem solvers and prevents local rate claims from exceeding the assumptions on curvature accuracy.

## Further reading

- Lee, Sun, and Saunders, [“Proximal Newton-Type Methods for Minimizing Composite Functions”](https://doi.org/10.1137/130921428), for globalization and local convergence results for exact and inexact composite Newton models.
- Becker, Fadili, and Ochs, [“On Quasi-Newton Forward-Backward Splitting: Proximal Calculus and Convergence”](https://doi.org/10.1137/18M1167152), for diagonal and low-rank metric proximal calculus.
- Chapters 113–115, for forward–backward splitting, local curvature backtracking, and variable-metric proximal maps.
