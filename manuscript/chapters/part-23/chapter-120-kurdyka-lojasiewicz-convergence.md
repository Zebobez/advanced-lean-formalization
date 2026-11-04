# Chapter 120 — Kurdyka–Łojasiewicz Convergence and Finite Length

> **Audience.** This chapter follows the global stationarity analysis in Chapter 118 and the local rate analysis in Chapter 119. It explains when a descent sequence converges as a whole, rather than merely having stationary cluster points.

In nonconvex optimization, descent alone does not force the iterates to converge. The objective values may decrease to a limit while the iterates move among several points with nearly the same value. A useful geometric inequality, combined with two quantitative certificates from the algorithm, rules out this behavior: the total distance traveled is finite.

The Kurdyka–Łojasiewicz framework packages that argument for smooth and nonsmooth methods. It is a convergence theorem with explicit proof obligations, not a magic property that can be attached to an algorithm after the fact.

## Learning objectives

After this chapter, you should be able to:

- state the KL inequality using a desingularizing function;
- distinguish sufficient decrease, relative error, and subsequential value continuity;
- explain why those hypotheses yield finite length and convergence of the entire sequence;
- recognize common classes of functions with the KL property;
- separate the mathematical theorem from the Lean proof kernel that telescopes descent;
- identify what remains to be proved before applying the theorem to a proximal Newton method.

## 1. From stationary cluster points to one limit

Suppose an algorithm generates iterates \(x_k\) and objective values \(F(x_k)\). If the objective decreases and is bounded below, then the scalar sequence \(F(x_k)\) converges. If the iterates are also bounded, they have cluster points. Neither fact implies that the entire iterate sequence converges: a bounded sequence can have several cluster points even when a scalar energy has a limit.

Chapter 118 established a common proximal Newton conclusion. Under uniform metric and line-search bounds, the accumulated squared direction norms are finite. This implies the directions vanish, and closedness of the subgradient graph then makes cluster points stationary. That is an important result, but the logical endpoint is still “every cluster point is stationary.” It does not identify the cluster points with one another.

The KL argument supplies the missing length estimate. A finite-length sequence satisfies
\[
\sum_{k=0}^{\infty}\|x_{k+1}-x_k\|<\infty.
\tag{120.1}
\]
For \(m>n\), the triangle inequality gives
\[
\|x_m-x_n\|
\le \sum_{k=n}^{m-1}\|x_{k+1}-x_k\|.
\tag{120.2}
\]
The tails of a convergent nonnegative series go to zero. Thus the iterates form a Cauchy sequence, and in finite-dimensional Euclidean space they converge. The proof therefore has two distinct jobs:

1. derive finite length from a descent inequality and KL geometry;
2. identify the limit as critical, using the relative-error condition and a value-continuity hypothesis.

## 2. The KL inequality

Let \(F:\mathbb{R}^n\to\mathbb{R}\cup\{+\infty\}\) be proper and lower semicontinuous. Write \(\partial F(x)\) for its limiting subdifferential and
\[
\operatorname{dist}(0,\partial F(x))
=\inf\{\|v\|:v\in\partial F(x)\}.
\]
A point is limiting-critical if \(0\in\partial F(x)\).

We say that \(F\) has the **Kurdyka–Łojasiewicz property** at a point \(\bar x\in\operatorname{dom}\partial F\) if there are a neighborhood \(U\) of \(\bar x\), a number \(\eta>0\), and a continuous, concave function
\[
\varphi:[0,\eta)\to\mathbb{R}_{\ge 0}
\]
such that \(\varphi(0)=0\), \(\varphi\) is continuously differentiable on \((0,\eta)\), \(\varphi'(s)>0\) for \(s>0\), and
\[
\varphi'\bigl(F(x)-F(\bar x)\bigr)
\operatorname{dist}(0,\partial F(x))\ge 1
\tag{120.3}
\]
whenever \(x\in U\) and
\[
F(\bar x)<F(x)<F(\bar x)+\eta.
\]

The function \(\varphi\) is called a **desingularizing function**. In the smooth case, \(\partial F(x)=\{\nabla F(x)\}\), so the inequality reads
\[
\varphi'\bigl(F(x)-F(\bar x)\bigr)\|\nabla F(x)\|\ge 1.
\]
The gradient may become small as the objective gap approaches zero. The desingularizing derivative grows to compensate, producing a uniform lower bound after the objective is reparameterized.

The property is local. It controls points close to \(\bar x\) whose function values lie in a specified interval. It says nothing about arbitrary iterates far from that neighborhood. This locality is why the convergence theorem first identifies a suitable cluster point and then applies a trapping argument to a sufficiently late tail of the sequence.

Many functions used in finite-dimensional optimization satisfy the KL property. In particular, proper lower-semicontinuous semialgebraic functions do, as do broad classes of functions definable in o-minimal structures. Polynomial and piecewise-polynomial models, norms, indicator functions of semialgebraic sets, and many composite objectives built from these ingredients are covered. The function need not be convex; it also need not be differentiable.

### 2.1 A simple KL calculation

For \(F(x)=\tfrac12 x^2\), take \(\bar x=0\). On \(x\ne0\), the limiting subdifferential is the ordinary gradient, \(\partial F(x)=\{x\}\). Choose
\[
\varphi(s)=\sqrt{2s}.
\]
Then \(\varphi'(s)=1/\sqrt{2s}\) and
\[
\varphi'(F(x))\,\operatorname{dist}(0,\partial F(x))
=\frac{1}{|x|}|x|=1.
\tag{120.4}
\]
Thus the square-root desingularizer gives an exact KL inequality near zero.

A second example is \(F(x)=|x|\) at \(\bar x=0\). For \(x\ne0\), \(\operatorname{dist}(0,\partial F(x))=1\). Taking \(\varphi(s)=s\) makes (120.3) an equality. This sharper desingularizer is consistent with the fact that soft thresholding reaches zero in finitely many steps.

## 3. The three certificates

Let \((x_k)_{k\ge0}\) be a sequence in \(\mathbb{R}^n\), and set \(s_k=\|x_{k+1}-x_k\|\). The abstract descent theorem uses constants \(a,b>0\) and three conditions.

**Sufficient decrease.** For every \(k\),
\[
F(x_{k+1})+a s_k^2\le F(x_k).
\tag{120.5}
\]
The objective decrease controls the squared step. In particular, \(F(x_k)\) is nonincreasing.

**Relative error.** For every \(k\), there exists \(w_{k+1}\in\partial F(x_{k+1})\) such that
\[
\|w_{k+1}\|\le b s_k.
\tag{120.6}
\]
The subgradient at the new iterate is small when the step producing that iterate is small. For a proximal method, this often follows from the optimality condition of the subproblem.

**Subsequential value continuity.** There is a subsequence \(x_{k_j}\to\bar x\) such that
\[
F(x_{k_j})\longrightarrow F(\bar x).
\tag{120.7}
\]
This is stronger than merely being a cluster point. Lower semicontinuity gives \(F(\bar x)\le\liminf_j F(x_{k_j})\), but that inequality alone does not give equality. Continuity of \(F\) on the relevant region is one simple way to obtain (120.7); for extended-valued objectives, it should be checked from the structure of the method.

These conditions are deliberately separated. An algorithm may satisfy (120.5) but have no usable subgradient estimate. It may satisfy (120.6) only at an approximate subproblem point, not at its actual accepted iterate. The theorem applies only after each required certificate is stated at the correct point and with a constant uniform over the tail.

### 3.1 The finite-length convergence theorem

Assume \(F\) is proper and lower semicontinuous, the sequence satisfies (120.5)–(120.7), and \(F\) has the KL property at the point \(\bar x\) in (120.7). Then the whole sequence converges to \(\bar x\), the limit is critical,
\[
0\in\partial F(\bar x),
\tag{120.8}
\]
and the sequence has finite length:
\[
\sum_{k=0}^{\infty}s_k<\infty.
\tag{120.9}
\]

The theorem is global in the sense that no local-minimum assumption is needed. The limit can be a saddle point or another non-minimizing critical point. What matters is that the algorithm has the three certificates and the objective has the KL property at the cluster point singled out by (120.7).

The role of the hypotheses is now transparent:

- (120.5) makes the objective values monotone and supplies a quadratic decrease budget;
- (120.6) turns the KL lower bound on subgradients into a bound involving successive step lengths;
- (120.7) aligns the objective limit with the value at the chosen cluster point;
- (120.3) converts a value gap into enough geometric sharpness to sum the step lengths.

## 4. Why the length is finite

Here is the central estimate. Restrict attention to a sufficiently late tail that lies in the KL neighborhood and whose objective values lie in the KL value interval. Write
\[
r_k=F(x_k)-F(\bar x)\ge0,\qquad
s_k=\|x_{k+1}-x_k\|.
\]
If \(s_{k-1}=0\) on this localized tail, (120.6) gives a zero subgradient at \(x_k\). The KL inequality rules out a positive value gap there; since the objective values decrease to \(F(\bar x)\), we have \(F(x_k)=F(\bar x)\), and (120.5) forces every later step to vanish. Thus the recurrence need only be applied while adjacent steps are nonzero. For such steps, apply (120.6) at \(x_k\), using the preceding displacement:
\[
\operatorname{dist}(0,\partial F(x_k))\le b s_{k-1}.
\]
The KL inequality at \(x_k\) then yields
\[
\varphi'(r_k)\ge \frac{1}{b s_{k-1}}.
\tag{120.10}
\]
Concavity of \(\varphi\) gives
\[
\varphi(r_k)-\varphi(r_{k+1})
\ge \varphi'(r_k)(r_k-r_{k+1}).
\tag{120.11}
\]
Combining (120.5), (120.10), and (120.11) gives
\[
\varphi(r_k)-\varphi(r_{k+1})
\ge \frac{a}{b}\frac{s_k^2}{s_{k-1}}.
\tag{120.12}
\]
Equivalently,
\[
s_k
\le \sqrt{\frac{b}{a}
\bigl(\varphi(r_k)-\varphi(r_{k+1})\bigr)s_{k-1}}.
\]
The elementary inequality \(2\sqrt{uv}\le u+v\) now yields
\[
2s_k\le s_{k-1}
+\frac{b}{a}\bigl(\varphi(r_k)-\varphi(r_{k+1})\bigr).
\tag{120.13}
\]
Summing over \(k\) telescopes the desingularized objective values. The remaining endpoint term is bounded, so the partial sums of the step lengths are bounded. Since the terms are nonnegative, the infinite length is finite.

The first iterate in this tail is chosen close enough to \(\bar x\) that the total length bound keeps every later iterate inside the KL neighborhood. This is the trapping step. It prevents the proof from using a local inequality at points that have already escaped its domain. The formal theorem makes this step precise by shrinking the value interval and choosing the tail index sufficiently late.

After finite length gives \(x_k\to x_\infty\), the relative-error bound and \(s_k\to0\) give \(w_{k+1}\to0\). The subsequential value condition, together with the fact that the objective values are monotone, identifies the limiting value with \(F(\bar x)\). Closedness of the limiting-subgradient graph then gives \(0\in\partial F(x_\infty)\), and the theorem’s local argument identifies \(x_\infty=\bar x\).

This proof outline is a useful guide to formalization: local membership, positive objective gaps, nonzero steps, and the zero-step case are separate obligations. A Lean proof should not hide them inside an unqualified division by \(s_{k-1}\).

## 5. Worked examples

### 5.1 Gradient descent on a quadratic

Let
\[
F(x)=\frac12x^2,\qquad x_{k+1}=(1-\tau)x_k,\qquad 0<\tau<1.
\]
Put \(q=1-\tau\), so \(0<q<1\). Then \(x_k=q^k x_0\), and
\[
s_k=|x_{k+1}-x_k|=\tau |x_k|.
\]
The objective decrease is
\[
F(x_k)-F(x_{k+1})
=\frac{1-q^2}{2}x_k^2
=\frac{2-\tau}{2\tau}s_k^2.
\]
Thus (120.5) holds with \(a=(2-\tau)/(2\tau)\). For (120.6), choose \(w_{k+1}=x_{k+1}\). Since
\[
|w_{k+1}|=q|x_k|=\frac{q}{\tau}s_k,
\]
the relative-error condition holds with \(b=q/\tau\). Finally \(x_k\to0\), \(F(x_k)\to F(0)\), so (120.7) holds. The KL calculation (120.4) completes the theorem’s hypotheses.

This example is simple enough to compute directly, yet it illustrates the modular theorem: quadratic decrease, a subgradient-to-step estimate, and the KL geometry are independent certificates. The theorem recovers convergence and finite length; the explicit formula reveals the stronger geometric rate \( |x_k|=q^k|x_0|\).

### 5.2 Proximal point for the absolute value

Consider the proximal iteration
\[
x_{k+1}=\operatorname{prox}_{\lambda|\cdot|}(x_k)
=\operatorname{sign}(x_k)\max\{|x_k|-\lambda,0\},
\qquad \lambda>0.
\tag{120.14}
\]
For \(x_0>0\), this is \(x_k=\max\{x_0-k\lambda,0\}\); the method reaches zero after finitely many steps. The proximal optimality condition says
\[
\frac{x_k-x_{k+1}}{\lambda}\in\partial |x_{k+1}|.
\tag{120.15}
\]
Thus the relative-error condition holds with \(b=1/\lambda\).

The proximal objective that defines \(x_{k+1}\) is strongly convex. Comparing its value at its minimizer with its value at \(x_k\) gives
\[
|x_{k+1}|+\frac{1}{2\lambda}|x_{k+1}-x_k|^2
\le |x_k|,
\tag{120.16}
\]
so sufficient decrease holds with \(a=1/(2\lambda)\). Since the sequence eventually equals zero, (120.7) is immediate. The KL inequality for \(|x|\) at zero uses \(\varphi(s)=s\). All hypotheses hold, and finite termination is visible directly.

The example also shows how a proximal optimality condition often supplies both the algorithmic certificate and the right subgradient. The proof still needs the constants and index alignment: the subgradient in (120.15) belongs to the new point and is bounded by the displacement of that same step.

## 6. KL exponents and rates

A common desingularizing function has the form
\[
\varphi(s)=c s^{1-\theta},
\qquad c>0,\quad 0\le\theta<1.
\tag{120.17}
\]
Its derivative is \(c(1-\theta)s^{-\theta}\), so (120.3) is equivalent, up to constants, to a gradient or subgradient lower bound proportional to the objective gap raised to \(\theta\):
\[
\operatorname{dist}(0,\partial F(x))
\ge C\bigl(F(x)-F(\bar x)\bigr)^\theta.
\tag{120.18}
\]
The exponent provides rate information for many descent methods satisfying suitable versions of the decrease and relative-error assumptions. Under common conventions, exponent zero corresponds to finite termination, exponents up to one-half give a linear rate, and exponents above one-half give a sublinear rate. Exact iterate and objective rates depend on the algorithmic hypotheses and on the exponent convention; verify the specific theorem before using the exponent as a rate claim.

For the quadratic \(F(x)=\tfrac12x^2\), (120.4) has \(\varphi(s)=\sqrt{2s}\), which corresponds to \(\theta=\tfrac12\), consistent with linear convergence of gradient descent. For the absolute value, \(\varphi(s)=s\), corresponding to \(\theta=0\), consistent with finite termination of the proximal iteration.

## 7. Applying the framework to proximal Newton

The preceding chapters provide parts of a KL convergence proof, but the application must be assembled carefully.

Chapter 118 derives a sufficient-decrease estimate for accepted proximal Newton steps under uniform lower bounds on step lengths and model curvature, together with control of inexactness. This can instantiate (120.5) with an explicit constant. Bounded level sets then provide cluster points, but one must still establish the value-continuity condition (120.7) for the chosen cluster point.

The delicate step is (120.6). Chapter 117’s inexact model residual is naturally a certificate at the candidate point \(y_k=x_k+d_k\), while a line search may accept \(x_{k+1}=x_k+\alpha_k d_k\). If \(\alpha_k<1\), then \(y_k\) and \(x_{k+1}\) differ. A subgradient bound at \(y_k\) is not automatically a bound at \(x_{k+1}\). Chapter 119 establishes eventual full-step acceptance under its local assumptions; after that point, candidate and accepted point coincide, which helps. A complete KL application must still derive a true-objective subgradient bound proportional to the accepted displacement, with constants uniform on the tail.

A disciplined proof plan is therefore:

1. record the actual accepted displacement \(s_k=\|x_{k+1}-x_k\|\);
2. extract a sufficient-decrease constant from the globalization proof;
3. construct \(w_{k+1}\in\partial F(x_{k+1})\) and prove \(\|w_{k+1}\|\le b s_k\);
4. identify a cluster point and verify convergence of the objective values along its subsequence;
5. verify the KL property at that point;
6. invoke the abstract finite-length theorem.

This is more informative than a blanket claim that “the objective is semialgebraic, so the iterates converge.” Semialgebraicity supplies the geometric inequality; it does not replace the algorithm-specific certificates.

## 8. Lean proof architecture

Lean is well suited to the scalar descent accounting, but the analytic hypotheses should be formalized at their natural mathematical level. Keep separate interfaces for:

- the iterate sequence and displacement norm;
- the objective-value decrease;
- the selected subgradient witness;
- the KL inequality and its neighborhood conditions;
- the finite-dimensional completeness argument.

A small algebraic kernel can combine the scalar KL, relative-error, sufficient-decrease, and concavity certificates into the product estimate, isolate the AM–GM step that turns (120.12) into (120.13), and telescope the resulting recurrence. The objective is not to formalize the full variational-analysis theorem in one declaration; it is to make these scalar steps reusable and transparent.

```lean
import Mathlib

open Filter
open scoped Topology

theorem finite_descent_budget
    (F q : ℕ → ℝ) (a lower : ℝ)
    (h_lower : ∀ n, lower ≤ F n)
    (h_step : ∀ n, F (n + 1) + a * q n ≤ F n)
    (N : ℕ) :
    a * ∑ n ∈ Finset.range N, q n ≤ F 0 - lower := by
  have htel : ∀ N, F N + a * ∑ n ∈ Finset.range N, q n ≤ F 0 := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        nlinarith [h_step N]
  have h := htel N
  have hl := h_lower N
  linarith

theorem kl_length_recurrence
    {sPrev sCurr scaledDrop : ℝ}
    (hPrev : 0 ≤ sPrev)
    (hDrop : 0 ≤ scaledDrop)
    (hProduct : sCurr ^ 2 ≤ sPrev * scaledDrop) :
    2 * sCurr ≤ sPrev + scaledDrop := by
  nlinarith [sq_nonneg (sPrev - scaledDrop)]

theorem kl_product_bound_of_certificates
    {a b sPrev sCurr slope grad gap drop : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hPrev : 0 ≤ sPrev)
    (hSlope : 0 ≤ slope)
    (hKL : 1 ≤ slope * grad)
    (hRelative : grad ≤ b * sPrev)
    (hDecrease : a * sCurr ^ 2 ≤ gap)
    (hConcavity : slope * gap ≤ drop) :
    a * sCurr ^ 2 ≤ b * sPrev * drop := by
  have hgradScaled := mul_le_mul_of_nonneg_left hRelative hSlope
  have hfactor : 1 ≤ slope * (b * sPrev) := by
    nlinarith [hKL, hgradScaled]
  have hdecreaseScaled := mul_le_mul_of_nonneg_left hDecrease hSlope
  have hstepScaled : slope * (a * sCurr ^ 2) ≤ drop := by
    nlinarith [hdecreaseScaled, hConcavity]
  have hfromFactor :=
    mul_le_mul_of_nonneg_right hfactor (mul_nonneg ha (sq_nonneg sCurr))
  have htoDrop := mul_le_mul_of_nonneg_left hstepScaled (mul_nonneg hb hPrev)
  nlinarith [hfromFactor, htoDrop]

theorem kl_partial_sum_bound
    (s phi : ℕ → ℝ) (c : ℝ)
    (hstep : ∀ k, 2 * s (k + 1) ≤ s k + c * (phi k - phi (k + 1)))
    (hs : ∀ k, 0 ≤ s k) (N : ℕ) :
    ∑ k ∈ Finset.range N, s (k + 1) ≤ s 0 + c * (phi 0 - phi N) := by
  have htel : ∀ N, (∑ k ∈ Finset.range N, s (k + 1)) + s N ≤
      s 0 + c * (phi 0 - phi N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        nlinarith [hstep N]
  have h := htel N
  linarith [hs N]

theorem kl_recurrence_summable
    (s phi : ℕ → ℝ) (c lower : ℝ)
    (hc : 0 ≤ c)
    (hphi : ∀ n, lower ≤ phi n)
    (hs : ∀ n, 0 ≤ s n)
    (hstep : ∀ k, 2 * s (k + 1) ≤ s k + c * (phi k - phi (k + 1))) :
    Summable s := by
  have hbound : ∀ N, ∑ k ∈ Finset.range N, s (k + 1) ≤
      s 0 + c * (phi 0 - lower) := by
    intro N
    have htel := kl_partial_sum_bound s phi c hstep hs N
    have hmul := mul_le_mul_of_nonneg_left (hphi N) hc
    nlinarith [htel, hs N]
  have htail : Summable fun n => s (n + 1) :=
    summable_of_sum_range_le (fun n => hs (n + 1)) hbound
  exact (summable_nat_add_iff (f := s) 1).mp htail

theorem finite_length_sequence_is_cauchy {X : Type*} [PseudoMetricSpace X]
    (x : ℕ → X)
    (h_length : Summable fun n => dist (x n) (x n.succ)) :
    CauchySeq x :=
  cauchySeq_of_summable_dist h_length

theorem finite_length_sequence_converges {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] (x : ℕ → X)
    (h_length : Summable fun n => dist (x n) (x n.succ)) :
    ∃ xLimit, Tendsto x atTop (𝓝 xLimit) :=
  cauchySeq_tendsto_of_complete (finite_length_sequence_is_cauchy x h_length)
```

Use \(q_k=s_k^2\) and \(a>0\). This theorem yields a uniform finite-horizon bound on partial sums of squared steps. Passing to an infinite sum is a separate order-theoretic step. It proves finite energy, not finite length: \(\sum s_k^2<\infty\) does not by itself imply \(\sum s_k<\infty\). The desingularizing recurrence (120.13) is the additional argument that upgrades square summability to finite length.

The product-bound theorem combines the scalar certificates: `hKL` is the desingularized subgradient lower bound, `hRelative` is relative error, `hDecrease` is sufficient decrease, and `hConcavity` bounds the desingularized value drop. Its conclusion is the denominator-free form of (120.12). The next theorem applies AM–GM to obtain (120.13). The finite-sum theorem formalizes the telescoping step after (120.13): every partial sum is bounded by the initial step and the desingularized objective drop, with the endpoint step retained in an intermediate inequality. The summability theorem then uses a lower bound on the desingularized values and nonnegative steps to prove that the step lengths are summable. The two sequence lemmas formalize the next topological step in Exercise 1: once the consecutive distances are summable, the iterates are Cauchy; in a complete space they converge. These results leave the function-space facts that establish the scalar certificates as hypotheses, rather than proving the full variational-analysis theorem.

In a fuller development, define a structure of descent data with fields for sufficient decrease and selected subgradient witnesses. Prove the finite-length result in a theorem that also accepts the KL modulus, neighborhood membership, and continuity evidence. Avoid encoding the entire limiting-subdifferential graph or semialgebraic geometry into the scalar telescope. A library theorem can represent those analytic facts as hypotheses and keep the Lean proof focused on the sequence-level reasoning.

## 9. Common failure modes

1. **Concluding iterate convergence from objective convergence.** A convergent objective sequence need not identify a unique cluster point.
2. **Stopping at finite energy.** Square summability of steps is weaker than finite length.
3. **Applying the KL inequality outside its neighborhood.** It is local and applies only in a specified objective-value interval.
4. **Assuming boundedness implies the value-continuity condition.** Lower semicontinuity gives only one inequality; equality along a cluster subsequence needs justification.
5. **Using a candidate-point residual at the accepted iterate.** Damping changes the point and may break the relative-error estimate.
6. **Forgetting the index shift.** To bound a subgradient at \(x_k\), use the relative-error certificate for the step from \(x_{k-1}\) to \(x_k\).
7. **Dividing by a zero step.** Handle a stationary or zero-step tail before using (120.10)–(120.12).
8. **Calling the limit a minimizer.** The theorem yields a critical point, not necessarily a local or global minimum.
9. **Reading a rate directly from an exponent without matching conventions.** Verify which KL exponent definition and which algorithmic hypotheses the rate theorem uses.
10. **Formalizing all analysis inside one proof.** Isolate subgradient, descent, value-continuity, and scalar-telescope interfaces.

## 10. Exercises

1. Prove that a finite-length sequence in a complete metric space is Cauchy.
2. Verify the KL inequality for \(\tfrac12 x^2\) at zero with \(\varphi(s)=\sqrt{2s}\).
3. Verify it for \(|x|\) at zero with \(\varphi(s)=s\).
4. Derive the sufficient-decrease constant \(a=(2-\tau)/(2\tau)\) for the quadratic gradient iteration.
5. Derive the relative-error constant \(b=(1-\tau)/\tau\) in the same example.
6. Prove (120.13) from (120.12) using \(2\sqrt{uv}\le u+v\).
7. Explain why the value-continuity hypothesis is stronger than lower semicontinuity along a convergent subsequence.
8. Show why \(\sum_k s_k^2<\infty\) does not imply \(\sum_k s_k<\infty\), using \(s_k=1/(k+1)\).
9. For the proximal iteration of \(|x|\), derive the optimality inclusion (120.15) directly from minimization of the scalar proximal objective.
10. Inspect an algorithm from Chapters 113–118 and identify the exact candidate subgradient that could establish (120.6).
11. Explain where eventual full steps from Chapter 119 help with the KL application and which estimate remains to be proved.
12. Extend the finite-descent Lean lemma to show that every finite partial sum is bounded by the same energy budget.

## 11. Chapter summary

The KL inequality provides local geometric information about how function values and subgradients behave near a critical point. A descent algorithm must also provide sufficient decrease, a relative subgradient error bound at the actual next iterate, and a subsequence along which the objective values converge to the value at its cluster point.

Together, these conditions imply finite length and convergence of the full sequence to a critical point. The Lean development should preserve that modular structure. First formalize the finite descent telescope, then add the KL recurrence and topological limit arguments as separate layers. In proximal Newton applications, check carefully that candidate-point optimality survives damping and becomes a bound at the accepted iterate.

## Further reading

- Attouch, Bolte, and Svaiter, [“Convergence of descent methods for semi-algebraic and tame problems: proximal algorithms, forward-backward splitting, and regularized Gauss-Seidel methods”](https://doi.org/10.1007/s10107-011-0484-9), for the abstract sufficient-decrease, relative-error, and KL convergence theorem.
- Kanzow and Lechner, [“An inexact regularized proximal Newton method for nonconvex and nonsmooth optimization”](https://link.springer.com/article/10.1007/s10589-024-00560-0), for a proximal Newton application using KL analysis.
- Chapter 118 establishes global stationarity of proximal Newton cluster points; Chapter 119 studies local rates and eventual full steps. This chapter explains the additional conditions that can turn those results into convergence of the whole sequence.


