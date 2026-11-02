# Chapter 117 — Inexact Proximal Newton Methods and Forcing Terms

> **Audience.** This chapter follows proximal Newton models from Chapter 116. It treats the inner subproblem as an iterative computation with a certified residual, then connects that residual to global descent, stationarity measures, and the accuracy schedule needed near a solution.

A proximal Newton step can be much more expensive than a gradient step. Solving every quadratic subproblem to high accuracy wastes work early in the optimization, when the local model itself is still crude. Inexact methods stop the inner solver once it has produced enough evidence for the outer step.

The central design choice is the forcing rule: how small must the inner residual be at iteration \(k\)? A fixed relative tolerance can certify descent throughout the run. A tolerance that tightens as the outer iterate approaches a solution is needed to retain fast local convergence. Formalizing both behaviors requires distinguishing the subproblem residual, the composite stationarity measure, and the line-search decrease.

## Learning objectives

After this chapter, you should be able to:

- define an inexact proximal Newton direction through a subgradient residual;
- derive a composite descent bound from a relative residual tolerance;
- use a composite Armijo test to globalize the approximate direction;
- relate a model residual to a proximal-gradient mapping;
- distinguish a global forcing rule from a local fast-convergence rule;
- represent inner accuracy and outer acceptance as separate Lean certificates.

## 1. Exact and inexact model steps

### 1.1 The local model

Let \(F(x)=f(x)+g(x)\), where \(f:\mathbb R^n\to\mathbb R\) is smooth and \(g\) is proper, closed, and convex. At \(x_k\), choose a symmetric positive-definite model matrix \(H_k\) and define
\[
m_k(y)
=f(x_k)+\langle\nabla f(x_k),y-x_k\rangle
+\frac12\|y-x_k\|_{H_k}^2+g(y).
\tag{117.1}
\]
The exact proximal Newton point minimizes \(m_k\). Its displacement \(d_k=y_k-x_k\) satisfies
\[
0\in\nabla f(x_k)+H_kd_k+\partial g(x_k+d_k).
\tag{117.2}
\]
The exact inclusion contains a subgradient witness \(v_k\in\partial g(x_k+d_k)\) with \(\nabla f(x_k)+H_kd_k+v_k=0\).

In an inexact method, an inner solver returns \(\widetilde d_k\) and a subgradient witness \(v_k\) that nearly satisfy this equation. Define the residual by
\[
r_k=\nabla f(x_k)+H_k\widetilde d_k+v_k,
\qquad
v_k\in\partial g(x_k+\widetilde d_k).
\tag{117.3}
\]
The equation is exact as a definition of \(r_k\); the approximation lies in how small the residual is. Keeping \(v_k\) explicit is useful because it turns a numerical solver's output into a proposition that Lean can consume.

### 1.2 A relative residual condition

Measure the residual in the dual metric of the quadratic model:
\[
\|r\|_{H_k^{-1}}^2:=\langle H_k^{-1}r,r\rangle,
\qquad
\|d\|_{H_k}^2:=\langle H_kd,d\rangle.
\tag{117.4}
\]
For a forcing parameter \(0\le\eta_k<1\), require
\[
\|r_k\|_{H_k^{-1}}\le\eta_k\|\widetilde d_k\|_{H_k}.
\tag{117.5}
\]
This compares like quantities: the residual is measured in the dual norm, while the direction is measured in the primal norm. The matrix identity
\[
\langle r_k,\widetilde d_k\rangle
\le\|r_k\|_{H_k^{-1}}\|\widetilde d_k\|_{H_k}
\tag{117.6}
\]
is the weighted Cauchy–Schwarz inequality that makes this choice effective.

Let
\[
\Delta_k
=\langle\nabla f(x_k),\widetilde d_k\rangle
+g(x_k+\widetilde d_k)-g(x_k).
\tag{117.7}
\]
The subgradient inequality at \(x_k+\widetilde d_k\) gives
\[
g(x_k+\widetilde d_k)-g(x_k)
\le\langle v_k,\widetilde d_k\rangle.
\tag{117.8}
\]
Using (117.3), then (117.5)–(117.6), yields the central estimate
\[
\Delta_k
\le-\|\widetilde d_k\|_{H_k}^2
+\langle r_k,\widetilde d_k\rangle
\le-(1-\eta_k)\|\widetilde d_k\|_{H_k}^2.
\tag{117.9}
\]
Thus any forcing bound \(\eta_k\le\bar\eta<1\) certifies a strict composite descent direction whenever \(\widetilde d_k\ne0\). The exact solve in Chapter 116 is the special case \(r_k=0\).

## 2. Globalizing the inexact step

### 2.1 Composite Armijo search

Let \(\sigma\in(0,1)\) and \(\rho\in(0,1)\). Starting from \(\alpha=1\), backtrack through \(1,\rho,\rho^2,\ldots\) until
\[
F(x_k+\alpha\widetilde d_k)
\le F(x_k)+\sigma\alpha\Delta_k.
\tag{117.10}
\]
Because \(\Delta_k<0\), acceptance gives a true decrease in the original composite objective. The test uses the actual function \(F\), not the quadratic model.

If \(g\) is convex, then \(g(x_k+\alpha\widetilde d_k)\le(1-\alpha)g(x_k)+\alpha g(x_k+\widetilde d_k)\) for \(0\le\alpha\le1\). If \(\nabla f\) is locally Lipschitz, the smooth term has a second-order remainder of order \(\alpha^2\). Hence \(F(x_k+\alpha\widetilde d_k)\le F(x_k)+\alpha\Delta_k+O(\alpha^2)\). Since \(\Delta_k<0\) and \(\sigma<1\), all sufficiently small positive step lengths satisfy (117.10); the geometric search terminates.

The forcing bound and the Armijo condition serve different purposes. Equation (117.9) proves that the proposed direction is useful. Equation (117.10) checks that the chosen distance along that direction decreases the true objective. An inner solve should not be declared acceptable merely because the outer line search happened to find a tiny step.

### 2.2 Why geometric backtracking terminates

The finite-termination claim can be made quantitative. Suppose that, on the segment under consideration, the gradient of \(f\) is \(L\)-Lipschitz in the Euclidean norm. The descent lemma and convexity of \(g\) give, for \(0\le\alpha\le1\),
\[
F(x_k+\alpha\widetilde d_k)
\le F(x_k)+\alpha\Delta_k
+\frac{L}{2}\alpha^2\|\widetilde d_k\|^2.
\]
Consequently, Armijo acceptance is guaranteed whenever
\[
\alpha\le \frac{2(1-\sigma)(-\Delta_k)}{L\|\widetilde d_k\|^2},
\qquad \Delta_k<0,
\]
with the zero-curvature case understood separately. The right side is positive. Since \(\rho^j\to0\), some backtracking index satisfies this bound. The proof is not a black-box appeal to “sufficiently small”: the strictly negative first-order term eventually dominates the quadratic remainder.

For a formal proof, it is often helpful to separate three statements: the descent lemma for \(f\), the interpolation inequality for \(g\), and a natural-number lemma saying that a geometric sequence eventually falls below a positive threshold. The line-search result then combines them. This decomposition also identifies exactly where local Lipschitz continuity enters.

### 2.3 A model decrease alternative

Some inner solvers can certify a decrease in the quadratic model more cheaply than they can expose a subgradient residual. Suppose an approximate candidate \(\widetilde y_k=x_k+\widetilde d_k\) satisfies
\[
m_k(\widetilde y_k)
\le m_k(x_k)-c\|\widetilde d_k\|_{H_k}^2
\tag{117.11}
\]
for a fixed \(c>0\). Expanding the model shows \(\Delta_k\le-(c+\tfrac12)\|\widetilde d_k\|_{H_k}^2\), which again certifies a descent direction. This criterion can be natural for primal-dual subproblem solvers that return a model gap.

The two certificates are not identical. A small stationarity residual controls first-order optimality; a model-value gap controls objective improvement. Choose the one that the inner solver can compute and prove its implication for the outer method. Do not silently substitute one for the other.

### 2.4 What the line search does not prove

An accepted Armijo step gives monotonicity of the objective values, and if \(F\) is bounded below then these values converge. It does not alone prove that the iterates converge, that every cluster point is stationary, or that the step sizes stay away from zero. Those conclusions usually require additional hypotheses: bounded sublevel sets or another compactness argument, uniform positive lower and upper bounds on the model matrices, and a stationarity argument that relates small accepted steps to small outer residuals.

This distinction is useful when designing theorem statements. A theorem about each line-search iteration should conclude decrease and termination. A separate global theorem can state the assumptions needed for cluster-point stationarity. A local theorem can add Hessian regularity and a forcing sequence. In Lean, this naturally leads to several theorems consuming different fields of the algorithm's invariant, instead of one oversized theorem with assumptions that are difficult to use.

## 3. Residuals and stationarity mappings

### 3.1 The composite gradient mapping

For a stepsize \(\tau>0\), define the proximal-gradient mapping
\[
G_\tau(x)
=\frac1\tau\left(x-\operatorname{prox}_{\tau g}
\bigl(x-\tau\nabla f(x)\bigr)\right).
\tag{117.12}
\]
For convex \(f\) and \(g\), \(G_\tau(x)=0\) exactly when \(0\in\nabla f(x)+\partial g(x)\). It is a useful stationarity measure even when \(g\) is nonsmooth, and unlike a bare gradient it respects the composite structure.

The local quadratic model also has a proximal-gradient mapping. At \(y_k=x_k+\widetilde d_k\), its smooth gradient is \(\nabla f(x_k)+H_k\widetilde d_k\). Define
\[
G_\tau^{m_k}(y)
:=\frac1\tau\left(y-\operatorname{prox}_{\tau g}
\bigl(y-\tau(\nabla f(x_k)+H_k(y-x_k))\bigr)\right).
\]
If \(v_k\in\partial g(y_k)\) and the residual satisfies (117.3), then
\[
\left\|G_\tau^{m_k}(y_k)\right\|
\le \|r_k\|.
\tag{117.13}
\]
To see this, proximal optimality gives \(y_k=\operatorname{prox}_{\tau g}(y_k+\tau v_k)\). The input to the model mapping is \(y_k-\tau(\nabla f(x_k)+H_k\widetilde d_k)\), which differs from \(y_k+\tau v_k\) by \(-\tau r_k\). Nonexpansiveness of the proximal map yields (117.13).

This bridge matters for adaptive accuracy rules. A solver may stop when a model stationarity mapping becomes small relative to the true composite mapping at \(x_k\). Such rules compare progress in the local model with the remaining outer error, rather than demanding the same absolute inner tolerance at every iteration.

The norm in (117.13) is Euclidean, even though the residual certificate (117.5) is measured in the dual model metric. If the eigenvalues of \(H_k\) lie between \(\mu>0\) and \(M\), then
\[
\|r_k\|\le\sqrt{M}\,\|r_k\|_{H_k^{-1}},
\qquad
\|\widetilde d_k\|_{H_k}\le\sqrt{M}\,\|\widetilde d_k\|.
\]
The first inequality converts an inverse-metric residual into an ordinary residual; the second converts a model norm into an ordinary direction norm. These inequalities are not interchangeable: the lower eigenvalue bound is needed for the reverse conversions. Recording which direction of conversion is used prevents a common spectral-bound error in both the mathematics and its formal proof.

### 3.2 Global and local forcing

A fixed \(\eta_k\le\bar\eta<1\) is enough for the descent estimate (117.9) and the finite Armijo search. It does not by itself imply superlinear convergence. To recover the fast local behavior of an accurate proximal Newton method, the inner error must become small relative to the outer stationarity measure.

A common design pattern requires a model mapping to satisfy
\[
\|G_\tau^{m_k}(y_k)\|
\le\eta_k\|G_\tau(x_k)\|,
\qquad
0\le\eta_k\le\bar\eta<1.
\tag{117.14}
\]
The uniform upper bound protects global descent, while \(\eta_k\to0\) asks for increasingly accurate subproblem solutions near stationarity. Under suitable local regularity and Hessian consistency, this is the type of forcing behavior used to preserve superlinear convergence. A quadratic rate requires stronger accuracy and smoothness assumptions.

In practice, the solver cost can be balanced against outer progress by using a loose but descent-safe tolerance early and tightening it as \(\|G_\tau(x_k)\|\) shrinks. For example, one can cap a positive power of a stationarity estimate by \(\bar\eta\). This is a policy template, not a universal theorem: the exact exponent and residual definition must match the local convergence result being used.

There are two scales in a useful forcing rule. First, the cap \(\bar\eta<1\) is iteration-independent and protects every nonzero direction from losing descent. Second, the variable part of \(\eta_k\) describes how much work to spend inside the model. It can depend on a computable outer residual, a previous residual, or a model-to-true mapping comparison. An implementation should clamp the chosen value into \([0,\bar\eta]\), and the proof should expose both inequalities rather than hide the clamp inside an opaque definition.

The residual criterion is also solver-agnostic. A coordinate-descent method may track violations of coordinatewise optimality; a primal-dual method may track a KKT residual; a semismooth Newton solver may produce a natural generalized-equation residual. Each can be connected to the same outer theorem after proving that its stopping statistic bounds the subgradient residual in the required metric. This adapter lemma is often the right abstraction boundary for a reusable formal library.

## 4. Worked examples

### 4.1 An approximate step for a sparse quadratic

Let
\[
f(x)=2(x-3)^2,\qquad g(x)=2|x|,\qquad x_k=0,\qquad H_k=4.
\tag{117.15}
\]
The exact model minimizer is \(y_k=2.5\), as in Chapter 116. Instead, suppose the inner solver returns \(\widetilde y_k=2\), so \(\widetilde d_k=2\). Since \(\widetilde y_k>0\), choose \(v_k=2\in\partial g(\widetilde y_k)\). The smooth gradient is \(f'(0)=-12\), and the residual is
\[
r_k=f'(0)+H_k\widetilde d_k+v_k=-12+8+2=-2.
\tag{117.16}
\]
Here \(\|r_k\|_{H_k^{-1}}=1\) and \(\|\widetilde d_k\|_{H_k}=4\), so (117.5) holds with \(\eta_k=\tfrac14\). The slope is \(\Delta_k=-12(2)+(4-0)=-20\), while the bound (117.9) gives \(\Delta_k\le-(1-\tfrac14)16=-12\), which is valid.

The true objective decreases from \(F(0)=18\) to \(F(2)=6\). With \(\sigma=\tfrac14\), the full step satisfies the Armijo condition because \(6\le18+\tfrac14(-20)=13\). The subproblem is not solved exactly, but the residual is enough to certify both a useful direction and an accepted outer step.

### 4.2 An anisotropic two-dimensional residual

Let \(H=\operatorname{diag}(1,9)\), choose \(d=(1,1)\), and let \(g=0\) with \(\nabla f(x)=(0,-6)\). Then the model residual is
\[
r=\nabla f(x)+Hd=(1,3),\qquad
\|r\|_{H^{-1}}=\sqrt2,\qquad
\|d\|_H=\sqrt{10}.
\]
The relative condition holds with \(\eta=1/\sqrt5\). The composite slope is \(\Delta=\langle(0,-6),(1,1)\rangle=-6\), and the residual estimate gives \(\Delta\le-(1-1/\sqrt5)10\). This example makes the geometry visible: the residual's second coordinate is discounted in the inverse metric because the model curvature in that direction is large. An unweighted comparison of \(\|r\|\) and \(\|d\|\) would obscure the cancellation built into the quadratic model.

### 4.3 Logistic regression with a changing inner tolerance

In regularized logistic regression, the proximal Newton subproblem is a weighted \(\ell_1\) quadratic. Coordinate descent can solve it approximately and produce a subgradient residual at the candidate. Far from a solution, the algorithm can stop once the residual is a fixed fraction of the model step norm, ensuring (117.9). Near a solution, it can reduce that fraction according to a composite gradient-mapping estimate as in (117.14).

This policy avoids two extremes: oversolving a crude early model and keeping the inner tolerance too loose near the minimizer. The resulting method still has separate proof obligations for finite line-search acceptance, global stationarity of cluster points, and local superlinear behavior. One conclusion should not be used as a substitute for the hypotheses of another.

## 5. Lean proof architecture

### 5.1 Keep the witness and norm bound together

An inexact direction certificate should contain:

1. the displacement \(\widetilde d_k\) and candidate \(y_k=x_k+\widetilde d_k\);
2. a subgradient witness \(v_k\in\partial g(y_k)\);
3. the residual equation (117.3);
4. positive definiteness of \(H_k\);
5. the relative residual inequality (117.5).

From this record, prove (117.9) once. The Armijo theorem then consumes the resulting negative slope, while local forcing theorems can consume stronger fields such as \(\eta_k\to0\) or the mapping inequality (117.14).

### 5.2 Respect primal and dual metrics

The residual bound mixes \(\|\cdot\|_{H^{-1}}\) and \(\|\cdot\|_H\). Give both norms explicit definitions and prove their Cauchy–Schwarz relation as a lemma. If the implementation uses Euclidean residuals, record lower and upper eigenvalue bounds for \(H_k\) and convert them to the weighted estimate. Hiding that conversion inside coercions can lead to a bound with the wrong matrix orientation.

### 5.3 Separate inner stopping from outer acceptance

Model-solving code should return a candidate and its residual evidence. The outer algorithm then evaluates the true objective and either accepts a step length or shrinks it. This modular boundary lets one replace coordinate descent with a dual solver without rewriting the Armijo proof.

The proof and data flow can be pictured as follows:

```text
inner model solver
   │  candidate, subgradient witness, residual
   ▼
residual certificate ──► composite descent bound ──┐
                                                    ├─► Armijo test ─► accepted step
true objective and trial step ─────────────────────┘
```

The upper path establishes that the direction has a negative composite slope. The lower path checks the actual objective at trial step lengths. Both meet at the acceptance test, but neither certificate replaces the other.

Forcing sequences introduce an indexed invariant. Prove \(0\le\eta_k\le\bar\eta<1\) for all \(k\) for global descent; prove \(\eta_k\to0\) separately for the local accuracy theorem. Keeping these facts distinct prevents a proof from using eventual accuracy to justify every early iteration.

### 5.4 Isolate the scalar inequality

After the Hilbert-space lemmas have established weighted Cauchy–Schwarz, the core descent step is only a scalar calculation. The following Lean kernel records its inputs explicitly; `step` is the model norm of the direction, `residual` is the dual-metric residual norm, and `inner` bounds the residual pairing.

```lean
import Mathlib

theorem residual_slope_bound
    {slope step residual inner eta : ℝ}
    (hstep : 0 ≤ step)
    (hresidual : residual ≤ eta * step)
    (hcauchy : inner ≤ residual * step)
    (hslope : slope ≤ -(step ^ 2) + inner) :
    slope ≤ -(1 - eta) * step ^ 2 := by
  have hproduct : residual * step ≤ eta * step ^ 2 := by
    calc
      residual * step ≤ (eta * step) * step :=
        mul_le_mul_of_nonneg_right hresidual hstep
      _ = eta * step ^ 2 := by ring
  nlinarith
```

The norm and subgradient analysis belongs in lemmas that produce `hresidual`, `hcauchy`, and `hslope`. This theorem should not know whether the vector space is represented as functions, finite coordinate vectors, or a Mathlib Euclidean space. Separating the scalar kernel makes it easy to reuse and keeps the nonlinear-optimization layer focused on the assumptions that generate those inequalities.

## 6. Common failure modes

1. **Using the residual equation without a norm bound.** The equation defines an error but does not limit its effect on descent.
2. **Measuring residual and direction in mismatched norms.** The dual metric \(H^{-1}\) is what makes (117.6) compatible with the model norm.
3. **Allowing \(\eta_k\ge1\).** Then (117.9) no longer guarantees a negative composite slope.
4. **Demanding \(\eta_k\to0\) for every global result.** A fixed bound below one can suffice for descent and line-search termination.
5. **Using a fixed tolerance to claim superlinear convergence.** Local fast rates generally require the relative inner error to vanish.
6. **Confusing the local model mapping with the true mapping.** The model is an approximation; (117.13) quantifies only how accurately it has been solved.
7. **Accepting an inner solve without outer line search.** A direction certificate does not guarantee that a full step decreases the actual objective.
8. **Claiming global convergence from Armijo decrease alone.** Boundedness, model-matrix conditions, and a stationarity argument are still required.

## 7. Exercises

1. Derive the relative residual descent estimate (117.9) from (117.3)–(117.8).
2. Show that if \(r_k=0\), the inexact certificate recovers the exact model decrease from Chapter 116.
3. Prove finite termination of the composite Armijo search under the assumptions in Section 2.1.
4. Derive the proximal-map comparison that yields (117.13).
5. Verify every residual and objective calculation in the sparse quadratic example.
6. Explain why a fixed forcing parameter \(\eta<1\) is sufficient for descent but not sufficient by itself for a superlinear rate.
7. Give a stopping rule for a coordinate-descent inner solver that returns a computable upper bound on \(\|r_k\|_{H_k^{-1}}\).
8. Design Lean structures for the inner residual certificate and outer Armijo certificate, and identify the theorem connecting them.
9. State extra assumptions needed to turn monotone objective decrease into convergence of the entire iterate sequence.
10. Compare the computational cost of an absolute residual tolerance and a relative forcing rule near a solution.
11. Prove each spectral comparison in Section 3.1 and identify the eigenvalue bound used in each direction.
12. In the two-dimensional example, compute the exact model minimizer and compare its displacement with the certified inexact displacement.

## 8. Chapter summary

Inexact proximal Newton methods replace exact solution of each composite quadratic model with a residual certificate. A relative bound in the model's dual and primal norms gives a negative composite slope; Armijo backtracking then converts that direction into decrease of the true objective. A forcing parameter bounded below one supports global descent, while tightening it near stationarity is the mechanism used to preserve fast local convergence.

For formalization, keep the inner witness, residual norm, local stationarity mapping, and outer acceptance proof separate. This allows solver-specific code to change while the descent and convergence arguments consume stable mathematical certificates.

## Further reading

- Lee, Sun, and Saunders, [“Proximal Newton-Type Methods for Minimizing Composite Functions”](https://doi.org/10.1137/130921428), for forcing conditions and global/local convergence results for inexact subproblems.
- Eisenstat and Walker, [“Choosing the Forcing Terms in an Inexact Newton Method”](https://doi.org/10.1137/0917003), for adaptive forcing sequences in Newton methods.
- Chapters 114–116, for adaptive curvature, proximal quasi-Newton models, and residual-based model descent.
