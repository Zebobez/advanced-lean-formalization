# Chapter 119 — Local Superlinear Convergence and Forcing Terms

> **Audience.** This chapter follows the global stationarity result of Chapter 118. It studies what changes near a solution when curvature models become accurate and inner solves become tighter, and explains why eventual acceptance of full steps is part of a local rate proof.

Global convergence identifies stationary cluster points under assumptions that control the whole run. Local convergence asks a sharper question: once the iterate is close to a particular solution, how quickly does the error shrink? Newton methods can reduce the error by more than a fixed factor, but only when curvature error, inner-solve error, and line-search damping all become small in compatible ways.

The proof strategy is modular. First derive an error recurrence for full steps. Then show the assumptions make its error ratio tend to zero. Finally, justify that the globalization accepts those full steps near the solution. In a composite problem, the proximal stationarity mapping takes the place of the ordinary gradient, and additional regularity is needed to transfer local model accuracy to the true problem.

## Learning objectives

After this chapter, you should be able to:

- state the difference between linear, superlinear, and quadratic convergence;
- derive a local error equation for an inexact Newton step;
- recognize the Dennis–Moré condition as directional curvature consistency;
- show how a vanishing forcing term removes first-order inner error;
- prove eventual full-step acceptance from a local model remainder;
- identify the extra error-bound or strong-regularity lemma needed in a composite proof.

## 1. Rates and the local setting

Let \(x^*\) be a solution and write \(e_k=x_k-x^*\). A sequence converges **q-linearly** if, for some \(q<1\), its error eventually satisfies \(\|e_{k+1}\|\le q\|e_k\|\). It converges **q-superlinearly** if
\[
\frac{\|e_{k+1}\|}{\|e_k\|}\longrightarrow0
\tag{119.1}
\]
whenever \(e_k\ne0\) eventually. It converges **q-quadratically** if \(\|e_{k+1}\|\le C\|e_k\|^2\) for some fixed \(C\) near the solution.

The distinction is about the ratio of consecutive errors. A small residual is not a rate. To prove superlinear convergence, show that every error contribution in the next-iterate equation is small relative to \(\|e_k\|\). For quadratic convergence, show that those contributions are of order \(\|e_k\|^2\).

We begin with the smooth unconstrained core. It isolates the Taylor and forcing arguments without the subgradient graph and proximal mapping. The next sections explain how to return to the composite setting of Chapters 116–118.

## 2. The inexact Newton error equation

Suppose \(f:\mathbb R^n\to\mathbb R\) is twice continuously differentiable near a stationary point \(x^*\), with \(\nabla f(x^*)=0\) and positive-definite Hessian
\[
A_*=\nabla^2f(x^*)\succ0.
\tag{119.2}
\]
An inexact Newton direction \(d_k\) with symmetric positive-definite model matrix \(H_k\) has residual
\[
r_k=\nabla f(x_k)+H_kd_k.
\tag{119.3}
\]
A full step sets \(x_{k+1}=x_k+d_k\). Since \(e_{k+1}=e_k+d_k\), rearranging (119.3) gives the exact error identity
\[
H_ke_{k+1}
=(H_k-A_*)e_k+\bigl(A_*e_k-\nabla f(x_k)\bigr)+r_k.
\tag{119.4}
\]
Each term has a separate interpretation:

- \((H_k-A_*)e_k\) is curvature-model error;
- \(A_*e_k-\nabla f(x_k)\) is Taylor remainder;
- \(r_k\) is inner-solve error.

This identity is the main local proof interface. It avoids expanding \(d_k\) and \(e_{k+1}\) independently, and it makes clear what a formal convergence theorem must bound.

### 2.1 A sufficient superlinear theorem

Assume \(x_k\to x^*\) and that the algorithm takes full steps for all sufficiently large \(k\). The local estimates below concern this tail of the sequence; Section 4 explains one route to eventual full-step acceptance.

Assume there is \(\mu>0\) such that \(H_k\succeq\mu I\) for all sufficiently large \(k\), and assume
\[
\|H_k-A_*\|\longrightarrow0,
\qquad
\|A_*e_k-\nabla f(x_k)\|=o(\|e_k\|),
\qquad
\|r_k\|=o(\|e_k\|).
\tag{119.5}
\]
Then (119.4) and \(\|H_k^{-1}\|\le1/\mu\) imply
\[
\|e_{k+1}\|=o(\|e_k\|).
\tag{119.6}
\]
For the Taylor term, continuous differentiability of \(\nabla f\) at \(x^*\) gives the little-o remainder in (119.5). Thus positive definiteness controls the inverse, while consistency and forcing make the right side of (119.4) negligible compared with the current error.

This is a sufficient condition for the Newton core, not a universal proximal Newton theorem. In quasi-Newton methods, full matrix convergence \(\|H_k-A_*\|\to0\) can be unnecessarily strong. The Dennis–Moré condition controls curvature error only in the direction actually taken.

### 2.2 From forcing terms to residual error

A common inexact Newton rule is
\[
\|r_k\|\le\eta_k\|\nabla f(x_k)\|.
\tag{119.7}
\]
Near a nondegenerate solution, the gradient and error are comparable: there are positive constants \(c_1,c_2\) with
\[
c_1\|e_k\|\le\|\nabla f(x_k)\|\le c_2\|e_k\|.
\tag{119.8}
\]
Therefore, if \(\eta_k\to0\), (119.7) implies \(r_k=o(\|e_k\|)\). A fixed small forcing bound generally yields only a fixed error contraction; a forcing term that vanishes removes the first-order inner error.

If the Hessian is Lipschitz near \(x^*\), exact Hessian models satisfy
\[
\|H_k-A_*\|=O(\|e_k\|),
\qquad
\|A_*e_k-\nabla f(x_k)\|=O(\|e_k\|^2).
\tag{119.9}
\]
Thus a residual of order \(O(\|e_k\|^2)\) yields quadratic convergence through (119.4). A residual that is merely \(o(\|e_k\|)\) gives superlinear convergence but need not give a quadratic rate.

## 3. Dennis–Moré curvature consistency

For quasi-Newton methods, it is often enough to control the matrix error along the step:
\[
\frac{\|(H_k-A_*)d_k\|}{\|d_k\|}\longrightarrow0.
\tag{119.10}
\]
This is the Dennis–Moré condition. It does not say that \(H_k\to A_*\) in operator norm. It says that the model has asymptotically correct curvature in the direction that the iteration uses.

The directional condition is powerful and subtle. The error identity (119.4) contains \((H_k-A_*)e_k\), not \((H_k-A_*)d_k\). A standard quasi-Newton proof needs a comparison lemma showing that the step is locally comparable to the current error and that directional consistency transfers to the error equation. Formalizing that comparison is a separate theorem; rewriting (119.10) as full matrix convergence silently strengthens the assumptions.

For exact Hessian models \(H_k=\nabla^2 f(x_k)\), a locally Lipschitz Hessian gives
\[
\|(H_k-A_*)d_k\|
\le L\|e_k\|\|d_k\|.
\tag{119.11}
\]
Hence (119.10) follows when \(x_k\to x^*\). This simple estimate is a useful test case for a formal library’s operator-norm and bilinear-form bounds.

## 4. Full-step acceptance near the solution

A direction can have a superlinear local model rate while the actual iterates remain damped. To transfer the rate, prove that Armijo eventually accepts \(\alpha_k=1\).

Return to the composite objective \(F=f+g\) and notation of Chapter 117. Write
\[
q_k=\|d_k\|_{H_k}^2.
\tag{119.12}
\]
Assume the global analysis or a local initialization argument has already established \(x_k\to x^*\), so that the iterates and directions eventually lie in the neighborhood where the local remainder estimates hold.

Assume the inner residual gives
\[
\Delta_k\le-(1-\eta_k)q_k,
\qquad \eta_k\to0.
\tag{119.13}
\]
Suppose the smooth Taylor remainder and model-Hessian mismatch give, for nearby iterates,
\[
F(x_k+d_k)-F(x_k)
\le\Delta_k+\left(\frac12+\varepsilon_k\right)q_k,
\qquad \varepsilon_k\to0.
\tag{119.14}
\]
The nonsmooth term \(g\) is already included exactly in \(\Delta_k\); the remainder comes from \(f\) and the difference between its local curvature and \(H_k\).

Subtract the Armijo target \(F(x_k)+\sigma\Delta_k\). Using (119.13), we obtain
\[
F(x_k+d_k)-F(x_k)-\sigma\Delta_k
\le
\left[\frac12+\varepsilon_k-(1-\sigma)(1-\eta_k)\right]q_k.
\tag{119.15}
\]
If \(0<\sigma<\tfrac12\), the bracket tends to \(\sigma-\tfrac12<0\). Therefore the full step satisfies Armijo for all sufficiently large \(k\) with \(d_k\ne0\). This argument separates three ingredients: model descent, second-order accuracy of the smooth model, and a line-search parameter below one half.

The assumptions behind (119.14) should be proved rather than hidden. One sufficient route is a locally Lipschitz Hessian for \(f\), uniform positive and bounded eigenvalues for \(H_k\), and a relative quadratic-form consistency estimate between \(H_k\) and \(\nabla^2f(x_k)\). In a composite problem, convexity of \(g\) is enough for the global descent certificate, but it does not by itself supply a local rate for the proximal solution map.

## 5. Returning to the composite problem

For \(F=f+g\), the stationarity condition is \(0\in\nabla f(x)+\partial g(x)\). The proximal-gradient mapping \(G_\tau(x)\) from Chapter 117 is a single-valued residual for this inclusion. The local model has its own mapping \(G_\tau^{m_k}\), and the inner solver can use a relative rule such as
\[
\|G_\tau^{m_k}(y_k)\|
\le\eta_k\|G_\tau(x_k)\|,
\qquad \eta_k\to0.
\tag{119.16}
\]
This is the composite analogue of making the Newton residual small relative to the outer error.

A local rate theorem still needs a bridge from mapping size to distance. Typical assumptions include strong metric regularity of the generalized equation, a local error bound relating \(\|G_\tau(x)\|\) to \(\|x-x^*\|\), and stability of the model’s proximal solution map as \(H_k\) approaches the true Hessian. With those ingredients, a proof aims to establish an error recurrence of the form
\[
\|e_{k+1}\|
\le C\|e_k\|^2+C\eta_k\|e_k\|+o(\|e_k\|).
\tag{119.17}
\]
If \(\eta_k\to0\), every term on the right is \(o(\|e_k\|)\), giving superlinear convergence. If the model and inner errors are both \(O(\|e_k\|^2)\), the recurrence gives a quadratic rate.

Equation (119.17) is an architectural target, not a consequence of (119.16) alone. The constants and even the right error measure depend on the local regularity theorem being used. In a formal proof, keep the mapping-to-distance estimate, model perturbation estimate, and residual estimate as named lemmas. Then the final recurrence is short and solver-independent. For a quadratic conclusion, the final little-o remainder must also be bounded by \(O(\|e_k\|^2)\), for example through Lipschitz Hessian and second-order model consistency.

## 6. Worked examples

### 6.1 A scalar forcing rule

Take \(f(x)=\tfrac12x^2\), whose minimizer is \(x^*=0\). Let \(H_k=1\) and choose
\[
d_k=-(1-\eta_k)x_k.
\tag{119.18}
\]
Then \(r_k=x_k+d_k=\eta_kx_k\), exactly satisfying \(|r_k|=\eta_k|\nabla f(x_k)|\). With a full step,
\[
x_{k+1}=\eta_kx_k.
\tag{119.19}
\]
If \(\eta_k=\tfrac14\), the method is q-linear with ratio one quarter. If \(\eta_k\to0\), it is q-superlinear. If \(\eta_k=O(|x_k|)\), it is q-quadratic. This example shows why the forcing sequence predicts a rate only after the outer iteration and acceptance rule are specified.

### 6.2 Quasi-Newton curvature on an active \(\ell_1\) region

Let
\[
F(x)=\tfrac12 a x^2-bx+\lambda|x|,
\qquad a>0,\quad b>\lambda>0.
\tag{119.20}
\]
The minimizer is \(x^*=(b-\lambda)/a>0\). Once \(x_k\) and the trial points remain positive, \(g(x)=\lambda|x|\) is the affine function \(\lambda x\) on this region. The composite problem there is the smooth quadratic \(\tfrac12a x^2-(b-\lambda)x\).

Use the model curvature \(H_k=a+\delta_k>0\) and solve the local model exactly. Since \(e_k=x_k-x^*\), its displacement and next error are
\[
d_k=-\frac{a}{a+\delta_k}e_k,
\qquad
e_{k+1}=\frac{\delta_k}{a+\delta_k}e_k.
\tag{119.21}
\]
If \(\delta_k\to0\), then \(|e_{k+1}|/|e_k|\to0\). If \(|\delta_k|\le C|e_k|\) and \(a+\delta_k\) stays bounded below, then \(|e_{k+1}|\le C'|e_k|^2\). The nonsmooth penalty has not disappeared from the global problem; locally, after the active sign is fixed, it contributes a linear term and the Newton rate is governed by curvature consistency.

## 7. Lean proof architecture

### 7.1 Make the rate recurrence the final interface

A local convergence development should expose separate certificates for:

1. the line-search state and eventual full-step condition;
2. the inner residual or proximal-mapping tolerance;
3. the model-curvature remainder;
4. the local error bound or strong-regularity estimate;
5. the final recurrence in the norm of the outer error.

The data flow is:

~~~text
Hessian consistency ─► Taylor/model error ─┐
                                           ├─► error recurrence ─► rate
inner forcing ───────► residual error ─────┤
local regularity ────► mapping-to-distance ┘
                                           ▲
local Armijo estimate ─► full steps ───────┘
~~~

The line-search result is not part of the algebraic rate recurrence, but it is required to identify the next iterate with the full Newton update. Keeping it separate makes the proof reusable for unit-step methods and for globally damped methods that eventually become undamped.

### 7.2 A scalar rate kernel

After analysis has produced a bound \(e_{k+1}\le C e_k^2+\eta_k e_k\), the local contraction step is elementary. Here the errors and constants are nonnegative real numbers.

```lean
import Mathlib

theorem local_rate_step
    {e eNext C eta q : ℝ}
    (he : 0 ≤ e)
    (hbound : eNext ≤ C * e ^ 2 + eta * e)
    (hfactor : C * e + eta ≤ q) :
    eNext ≤ q * e := by
  have hmul := mul_le_mul_of_nonneg_right hfactor he
  nlinarith [hbound, hmul]

theorem geometric_error_bound
    {e : ℕ → ℝ} {q : ℝ}
    (hq : 0 ≤ q)
    (hstep : ∀ k, e (k + 1) ≤ q * e k)
    (n : ℕ) :
    e n ≤ q ^ n * e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        e (n + 1) ≤ q * e n := hstep n
        _ ≤ q * (q ^ n * e 0) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * e 0 := by rw [pow_succ]; ring
```

If both \(e_k\to0\) and \(\eta_k\to0\), then \(C e_k+\eta_k\to0\). The scalar lemma supplies an eventual contraction by any chosen \(q>0\), which is the final step in the superlinear-rate argument. The second lemma propagates a uniform contraction into the explicit bound \(e_n\le q^n e_0\); when \(q<1\), this is the usual geometric rate estimate. These lemmas do not prove the analytic recurrence; that should be a separate theorem with its model, residual, and regularity assumptions visible.

## 8. Common failure modes

1. **Calling a fixed small forcing term superlinear.** A fixed relative residual generally leaves a nonzero asymptotic error ratio.
2. **Using \(\eta_k\to0\) without relating the residual to outer error.** The tolerance must control the error term in the next-iterate equation.
3. **Assuming Hessian approximation automatically gives superlinear convergence.** Curvature consistency must hold in the relevant direction and the model solve must be accurate.
4. **Replacing Dennis–Moré with operator-norm convergence.** That may be a stronger assumption than the quasi-Newton theorem requires.
5. **Skipping eventual full-step acceptance.** A fast direction with persistent damping need not yield a superlinear iterate sequence.
6. **Using nonsmoothness as if it had a Taylor expansion.** Keep \(g\) in the proximal model; apply Taylor estimates to \(f\).
7. **Claiming quadratic convergence from a vanishing residual alone.** Quadratic rate needs second-order-size model and inner errors.
8. **Applying the smooth Newton theorem directly to a composite objective.** The proximal mapping and its local regularity need their own transfer lemmas.

## 9. Exercises

1. Derive the error identity (119.4) from the residual equation.
2. Prove that (119.5) implies (119.6), using the uniform inverse bound on \(H_k\).
3. Show that \(\|r_k\|\le\eta_k\|\nabla f(x_k)\|\) implies \(r_k=o(\|e_k\|)\) under (119.8) when \(\eta_k\to0\).
4. Verify the quadratic error claims in (119.9) for a locally Lipschitz Hessian.
5. Explain why the Dennis–Moré condition (119.10) does not imply \(\|H_k-A_*\|\to0\).
6. Derive the coefficient in (119.15), and state exactly why \(\sigma<1/2\) is used.
7. For the scalar forcing example, calculate the convergence rate for \(\eta_k=c|x_k|^p\) with \(c>0\).
8. In the \(\ell_1\) example, identify a neighborhood in which the active sign remains positive and verify (119.21).
9. List the additional lemmas needed to turn (119.16) into a theorem about \(\|x_{k+1}-x^*\|/\|x_k-x^*\|\).
10. Formalize the scalar rate kernel and then state the sequence-limit result that turns \(\eta_k\to0\), \(e_k\to0\) into a superlinear rate.
11. Give an example where the direction model is accurate but line-search damping prevents the claimed rate.
12. Compare a residual tolerance of order \(O(\|e_k\|)\), \(o(\|e_k\|)\), and \(O(\|e_k\|^2)\).

## 10. Chapter summary

Local superlinear convergence requires first-order errors to vanish relative to the current error. The Newton error identity separates curvature mismatch, Taylor remainder, and inner residual. Exact Hessians with Lipschitz variation give a quadratic model error; a forcing sequence that tends to zero gives a superlinear residual contribution. For quasi-Newton methods, the Dennis–Moré condition supplies directional rather than full matrix consistency.

In the composite setting, one also proves a local model-to-true stationarity estimate and eventual acceptance of full steps. Formalize those as independent interfaces before combining them into the final error recurrence. A small forcing parameter, by itself, is never the whole rate theorem.

## Further reading

- Lee, Sun, and Saunders, [“Proximal Newton-Type Methods for Minimizing Composite Functions”](https://doi.org/10.1137/130921428), for inexact proximal Newton forcing conditions and local rate results.
- Kanzow and Lechner, [“Globalized inexact proximal Newton-type methods for nonconvex composite functions”](https://link.springer.com/article/10.1007/s10589-020-00243-6), for eventual full-step acceptance and local linear or superlinear convergence under additional assumptions.
- Eisenstat and Walker, [“Choosing the Forcing Terms in an Inexact Newton Method”](https://doi.org/10.1137/0917003), for adaptive inexact Newton tolerances.
- Chapter 118 establishes global stationarity; this chapter supplies the local accuracy and rate layer.
