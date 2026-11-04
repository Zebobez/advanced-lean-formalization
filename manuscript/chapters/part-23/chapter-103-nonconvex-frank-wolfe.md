# Chapter 103 — Nonconvex Frank–Wolfe and Stationarity Certificates

> **Audience.** This chapter assumes the linear minimization oracle and curvature framework from Chapter 98. It drops convexity of the objective and studies what the Frank–Wolfe gap certifies when global optimality can no longer be inferred from a first-order inequality.

For a convex objective, the Frank–Wolfe gap bounds objective suboptimality. For a nonconvex objective, that interpretation fails: a stationary point can be a saddle or a local minimum with a worse value than another feasible point. The same gap still has a precise role. It measures violation of the first-order variational inequality for the feasible set.

The basic convergence proof also survives the loss of convexity. A finite curvature bound controls the objective change along each feasible segment. The line-search or quadratic-model step then decreases the objective whenever the gap is positive. Summing those decreases proves that at least one iterate has a small stationarity gap, with a best-iterate rate of \(O(1/\sqrt{T})\).

## Learning objectives

After this chapter, you should be able to:

- define constrained first-order stationarity for a differentiable objective;
- prove that the Frank–Wolfe gap vanishes exactly at a variationally stationary point;
- distinguish stationarity from global optimality and from a zero gradient;
- state the curvature inequality and derive a best-iterate gap rate;
- design Lean interfaces for an exact linear oracle, curvature bound, and finite descent sum.

## 1. Stationarity without convexity

### 1.1 The feasible variational inequality

Let \(\mathcal K\) be a nonempty compact convex set in a finite-dimensional inner-product space, and let \(f\) be differentiable but not necessarily convex. A feasible point \(x\in\mathcal K\) is **first-order stationary for the constrained problem** if

\[
\langle\nabla f(x),y-x\rangle\ge0
\qquad\text{for every }y\in\mathcal K.
\tag{103.1}
\]

This condition says that no feasible first-order direction decreases the objective. It is the variational inequality associated with \(\nabla f(x)\). In normal-cone terminology, it is equivalent to
\(-\nabla f(x)\in N_{\mathcal K}(x)\), with
\(N_{\mathcal K}(x)=\{n:\langle n,y-x\rangle\le0\ \forall y\in\mathcal K\}\).

Every differentiable local minimizer over a convex feasible set satisfies (103.1), by taking one-sided directional derivatives along segments to feasible points. The converse is false for nonconvex \(f\). Stationarity is a first-order necessary condition, not a global or even local sufficient condition.

### 1.2 The Frank–Wolfe gap characterizes this condition

At \(x\), choose an exact linear minimizer

\[
s(x)\in\arg\min_{s\in\mathcal K}\langle\nabla f(x),s\rangle
\tag{103.2}
\]
and define the gap

\[
g_{\mathrm{FW}}(x)
=\langle\nabla f(x),x-s(x)\rangle
=\max_{y\in\mathcal K}\langle\nabla f(x),x-y\rangle.
\tag{103.3}
\]

Compactness ensures that the maximum is attained. The gap is nonnegative because \(x\) itself is feasible. If \(g_{\mathrm{FW}}(x)=0\), then every feasible \(y\) satisfies
\(\langle\nabla f(x),x-y\rangle\le0\), which is exactly (103.1). Conversely, if (103.1) holds, all terms in the maximum are nonpositive and the choice \(y=x\) gives zero. Therefore

\[
g_{\mathrm{FW}}(x)=0
\quad\Longleftrightarrow\quad
x\text{ satisfies the constrained first-order condition (103.1).}
\tag{103.4}
\]

This is an exact certificate when the oracle is exact. With an approximate linear oracle, the reported gap is only an approximation to the maximum; a stopping theorem must retain the oracle error.

At an interior point of a full-dimensional set, every sufficiently small direction and its negative are feasible, so (103.1) forces \(\nabla f(x)=0\). At a boundary point, the gradient need not vanish. The feasible geometry can block all descent directions even when the ambient gradient is nonzero.

### 1.3 What convexity used to give

If \(f\) is convex, the first-order convexity inequality gives
\(f(x)-f(x^\star)\le g_{\mathrm{FW}}(x)\). This is why the gap in Chapter 98 served both as a stationarity measure and as an objective-error bound.

Without convexity, that inequality is unavailable. A small FW gap only shows that no feasible direction has a large negative directional derivative at the current point. The objective may have a better basin elsewhere, separated by a region of higher values. Keep the gap theorem and the objective-suboptimality theorem as separate statements with separate assumptions.

### 1.4 When the gap controls the gradient norm

At an interior point with a feasible ball of radius \(r>0\), the gap also gives a norm-gradient estimate. Choose a unit direction \(u\) with \(\langle\nabla f(x),u\rangle=\|\nabla f(x)\|_*\). Since \(x-ru\in\mathcal K\),
\[
g_{\mathrm{FW}}(x)\ge
\langle\nabla f(x),x-(x-ru)\rangle
=r\|\nabla f(x)\|_*.
\]
Therefore a small gap forces a small dual gradient norm when the point has known interior radius. At a boundary point, the available inward directions may have no such radius, so this implication can fail even at an exact constrained solution. The gap remains useful because it measures only feasible descent and does not require an interiority assumption.

The inner-product pairing also explains the affine-invariant character of the criterion. Under an invertible affine change of coordinates, gradients transform as covectors and feasible directions transform as vectors; their pairing, and hence the FW gap, is unchanged. A raw Euclidean gradient norm generally changes under the same coordinate transformation.

## 2. Curvature controls descent

### 2.1 A segment inequality for nonconvex functions

Define the curvature constant of a differentiable function over \(\mathcal K\) by

\[
C_f=
\sup_{\substack{x,s\in\mathcal K\\0<\gamma\le1}}
\frac{2}{\gamma^2}
\left[
f(x+\gamma(s-x))-f(x)
-\gamma\langle\nabla f(x),s-x\rangle
\right].
\tag{103.5}
\]

The definition does not require convexity of \(f\). It packages the largest quadratic remainder along feasible segments. For any \(C\ge C_f\),

\[
f(x+\gamma(s-x))
\le f(x)+\gamma\langle\nabla f(x),s-x\rangle
+\frac{C\gamma^2}{2}.
\tag{103.6}
\]

If \(\nabla f\) is \(L\)-Lipschitz on \(\mathcal K\) and its diameter is \(D\), then \(C_f\le LD^2\). Thus bounded curvature is implied by the usual smoothness-and-bounded-domain assumptions, but it is the more direct quantity for the line-search proof.

For the LMO atom \(s_t=s(x_t)\), the linear term in (103.6) is \(-\gamma g_t\). Choosing the model step

\[
\gamma_t=\min\left\{\frac{g_t}{C},1\right\},
\qquad
x_{t+1}=x_t+\gamma_t(s_t-x_t),
\tag{103.7}
\]

keeps the next iterate feasible. The same descent bound also holds for exact line search, since the line search can do at least as well as any particular feasible model step.

### 2.2 Per-iteration decrease

If \(0\le g_t\le C\), then \(\gamma_t=g_t/C\), and (103.6) yields

\[
f(x_t)-f(x_{t+1})\ge\frac{g_t^2}{2C}.
\tag{103.8}
\]

If \(g_t>C\), the method takes a full step \(\gamma_t=1\), and

\[
f(x_t)-f(x_{t+1})
\ge g_t-\frac C2
\ge\frac{g_t}{2}.
\tag{103.9}
\]

Thus a nonzero gap forces descent. Notice what is absent: no convexity inequality comparing \(f(x_t)\) with a global minimizer is used in (103.8)–(103.9). The proof needs only the oracle gap and the segment-curvature upper bound.

### 2.3 Best-iterate stationarity rate

Compactness and continuity give a global minimum \(f_{\min}=\min_{x\in\mathcal K}f(x)\), even though \(f\) is nonconvex. Set \(h_0=f(x_0)-f_{\min}\ge0\). The objective values decrease by (103.8)–(103.9), so their total decrease over \(T\) steps is at most \(h_0\).

Let \(\delta_T=\min_{0\le t<T}g_t\). If \(\delta_T\le C\), every iteration decreases the objective by at least \(\delta_T^2/(2C)\): for a gap above \(C\), (103.9) is at least \(C/2\), which is no smaller than \(\delta_T^2/(2C)\). Summing gives
\(\delta_T\le\sqrt{2Ch_0/T}\). If \(\delta_T>C\), every iteration decreases by at least \(\delta_T/2\), giving \(\delta_T\le2h_0/T\). Consequently,

\[
\min_{0\le t<T}g_t
\le
\max\left\{\sqrt{\frac{2Ch_0}{T}},\frac{2h_0}{T}\right\}
=O(T^{-1/2}).
\tag{103.10}
\]

The theorem concerns the best gap encountered, not necessarily the last iterate’s gap. To return an approximate stationary point, store the iterate with smallest certified gap. For a target \(\varepsilon\le C\), the first term gives the familiar \(O(Ch_0/\varepsilon^2)\) iteration guarantee. Stronger assumptions can improve this rate, but no convex objective-gap statement follows here.

The rate is deterministic and concerns objective decrease, not convergence of the entire sequence. Several iterates may have larger gaps after a low-gap point, because the gap is not generally monotone. A common proof mistake is to combine a bound on \(\min_t g_t\) with a claim about \(g_T\). The conclusion gives an existential index and should be reflected in the algorithm output.

The proof flow is:

~~~text
global linear oracle ──> nonnegative FW gap
                                  |
curvature inequality ────────────┴──> one-step objective decrease
                                              |
global lower bound on f ─────────────────────┘
                                              |
                                  sum decreases over T steps
                                              |
                                              v
                                   a small FW gap exists
~~~

### 2.4 Approximate linear oracles

Suppose the oracle returns a feasible \(s_t\) whose linear value is within \(\varepsilon_t\) of the true minimum:

\[
\langle\nabla f(x_t),s_t\rangle
\le \min_{y\in\mathcal K}\langle\nabla f(x_t),y\rangle+\varepsilon_t.
\tag{103.11}
\]

Let \(G_t\) denote the exact FW gap and let \(\widehat g_t=\langle\nabla f(x_t),x_t-s_t\rangle\) be the achieved gap. Rearranging (103.11) gives \(G_t\le\widehat g_t+\varepsilon_t\). Thus a small achieved gap certifies near-stationarity only after adding the oracle error. The one-step descent proof also uses the achieved gap, not the unavailable exact maximum. If \(\widehat g_t>0\), use it in the model step. If \(\widehat g_t\le0\), the error certificate already gives \(G_t\le\varepsilon_t\), so the point is approximately stationary and the algorithm can stop at that tolerance.

For a run with varying \(\varepsilon_t\), keep each error bound attached to its iterate. A theorem can state a best-iterate guarantee for the achieved gaps, then convert it to a true-gap guarantee by adding the error of the returned index. Replacing every \(\varepsilon_t\) by a single maximum is simpler but may obscure a much more accurate late-stage oracle. As in Chapter 98, the approximate-oracle statement belongs in the interface: do not silently treat the returned atom as an exact minimizer.

## 3. Two worked examples

### 3.1 A stationary point that is not globally optimal

Let \(\mathcal K=[0,1]\) and
\[
f(x)=x-6x^2+8x^3.
\]
At \(x=0\), \(f'(0)=1\). The linear oracle minimizes \(s\mapsto s\) over \([0,1]\), so it returns \(s=0\). The FW gap is \(1\cdot(0-0)=0\), and \(x=0\) satisfies the constrained first-order condition because all feasible directions point to the right.

But at \(x=1/3\),
\[
f(1/3)=\frac13-\frac{6}{9}+\frac{8}{27}
=-\frac1{27}<f(0)=0.
\]
Thus the gap correctly certifies constrained stationarity while failing to claim global optimality. In fact, because \(f'(0)>0\), the boundary point is a local minimum on the interval; the lower value lies in another basin.

The Lean calculation separates the variational certificate from the objective values. It verifies the derivative at the boundary, nonnegative feasible directional derivatives, a local minimum near zero, and a lower feasible value at one third.

```lean
def nonconvexObjective103 : ℝ → ℝ :=
  (fun x : ℝ => x) - (fun x => 6 * x ^ 2) + (fun x => 8 * x ^ 3)

theorem nonconvexObjective103_deriv_at_zero :
    HasDerivAt nonconvexObjective103 1 0 := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id 0
  have hsquare : HasDerivAt (fun x : ℝ => x ^ 2) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ))
  have hcube : HasDerivAt (fun x : ℝ => x ^ 3) 0 0 := by
    simpa using (hasDerivAt_pow 3 (0 : ℝ))
  have hsix : HasDerivAt (fun x : ℝ => 6 * x ^ 2) 0 0 := by
    simpa using hsquare.const_mul (6 : ℝ)
  have height : HasDerivAt (fun x : ℝ => 8 * x ^ 3) 0 0 := by
    simpa using hcube.const_mul (8 : ℝ)
  change HasDerivAt
    ((fun x : ℝ => x) - (fun x => 6 * x ^ 2) + (fun x => 8 * x ^ 3)) 1 0
  simpa using (hid.sub hsix).add height

theorem nonconvexObjective103_at_zero : nonconvexObjective103 0 = 0 := by
  norm_num [nonconvexObjective103]

theorem boundary_fw_gap_zero : (1 : ℝ) * (0 - 0) = 0 := by norm_num

theorem boundary_variational_condition (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (1 : ℝ) * (y - 0) := by
  rcases hy with ⟨hy0, hy1⟩
  nlinarith

theorem nonconvex_boundary_is_local_minimum (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 4) :
    nonconvexObjective103 0 ≤ nonconvexObjective103 x := by
  have hfactor : nonconvexObjective103 x = x * (1 - 2 * x) * (1 - 4 * x) := by
    simp [nonconvexObjective103]
    ring
  rw [nonconvexObjective103_at_zero, hfactor]
  have h2 : 0 ≤ 1 - 2 * x := by linarith
  have h4 : 0 ≤ 1 - 4 * x := by linarith
  exact mul_nonneg (mul_nonneg hx0 h2) h4

theorem nonconvexObjective103_at_one_third :
    nonconvexObjective103 (1 / 3) = -(1 : ℝ) / 27 := by
  norm_num [nonconvexObjective103]
```

### 3.2 A nonzero gradient at a constrained optimum

Let \(\mathcal K\) be the Euclidean ball of radius \(R\), and minimize the linear objective \(f(x)=\langle a,x\rangle\) for \(a\ne0\). The optimizer is
\(x^\star=-R a/\|a\|_2\), where the gradient is still \(a\), so \(\|\nabla f(x^\star)\|_2=\|a\|_2>0\). The LMO returns \(s(x^\star)=x^\star\), and the gap is zero.

More generally, the ball oracle gives
\[
s(x)=-R\frac{\nabla f(x)}{\|\nabla f(x)\|_2}
\]
when the gradient is nonzero, so
\[
g_{\mathrm{FW}}(x)
=\langle\nabla f(x),x\rangle+R\|\nabla f(x)\|_2.
\]
At a boundary optimum this vanishes even though the ambient gradient does not. A criterion based only on \(\|\nabla f(x)\|\) would misclassify this constrained solution.

### 3.3 Read the rate as an iteration certificate

Suppose the curvature upper bound is \(C=2\), the initial objective excess is \(h_0=1\), and the algorithm runs for \(T=100\) steps. Equation (103.10) gives
\[
\min_{0\le t<100}g_t
\le\max\left\{\sqrt{\frac{4}{100}},\frac{2}{100}\right\}
=0.2.
\]
The output is one of the 100 recorded points, chosen by its gap; the theorem does not identify in advance which index wins. If the target is \(\varepsilon=0.05\), the first branch requires \(T\ge 2Ch_0/\varepsilon^2=1600\), while the second branch requires only \(T\ge 2h_0/\varepsilon=40\). The larger requirement controls. Reporting the two regimes makes the meaning of the asymptotic \(O(1/\varepsilon^2)\) statement concrete.

## 4. Lean proof architecture

### 4.1 State the stationarity predicate directly

For a point \(x\), define a proposition expressing feasibility and
\(\forall y\in\mathcal K,\ \langle\nabla f(x),y-x\rangle\ge0\). Prove it equivalent to zero FW gap using:

1. feasibility of \(x\), which gives a zero candidate in the maximum;
2. optimality of the LMO, which identifies the maximum with the oracle expression;
3. compactness, which provides an attaining point if the gap is defined as a maximum.

This theorem is independent of convexity of \(f\). If the library defines the normal cone with the opposite sign convention, prove the sign conversion once in a named lemma.

### 4.2 Keep curvature and smoothness as alternatives

One interface can assume the segment inequality (103.6) directly. A separate lemma derives it from an \(L\)-Lipschitz gradient and diameter bound. This avoids forcing every application to prove a global gradient-Lipschitz estimate when a sharper curvature bound is known.

Represent the step-size rule with a case split on \(g_t\le C\). The two decrease lemmas then have simple hypotheses and avoid divisions by zero if \(C>0\) is a field of the curvature-bound structure. The zero-curvature case can be handled separately or by choosing any positive \(C\ge C_f\).

### 4.3 Prove the finite sum before the minimum-gap conclusion

A sequence theorem should assume:

- \(f_{t+1}\le f_t\);
- each step with gap at most \(C\) decreases by at least \(g_t^2/(2C)\);
- each step with gap above \(C\) decreases by at least \(g_t/2\);
- \(f_t\ge f_{\min}\).

For a finite index interval, split on whether the minimum gap is at most \(C\). Sum the matching per-step decrease and derive (103.10). This proof is real arithmetic and finite summation; it should not unfold the LMO, the feasible set, or the gradient.

If the returned point is selected by an argmin over a finite list of gaps, make the list and index set part of the algorithm output. The mathematical theorem guarantees existence of a small-gap index; the implementation must preserve that index so that the certified iterate can actually be returned.

One clean data design returns a pair consisting of an index \(i:\mathrm{Fin}(T)\) and the iterate \(x_i\), together with a proof that its gap is no larger than every stored gap. A separate theorem then instantiates the existence bound from the finite-sum argument. This avoids asking Lean to compute a minimizer over the real set \(\mathcal K\): only the finite list of already computed oracle gaps is searched. If those values are interval-enclosed approximations, the selection certificate must compare upper bounds for the chosen gap and lower bounds for competitors, or return an index whose certified upper bound meets tolerance.

## 5. Common failure modes

1. **Calling the gap a primal-dual objective gap.** That interpretation requires convexity.
2. **Calling every stationary point a minimizer.** Nonconvex objectives can have stationary saddles and suboptimal local minima.
3. **Demanding a zero gradient at the boundary.** Constrained stationarity is a variational inequality.
4. **Claiming last-iterate convergence from a best-iterate theorem.** The bound is on the minimum gap encountered.
5. **Using curvature as if it required convexity.** The segment upper bound is valid for nonconvex differentiable objectives too.
6. **Forgetting a lower bound on objective values.** Descent summation needs \(f(x_t)\ge f_{\min}\).
7. **Normalizing a zero gradient in the oracle formula.** Handle that branch separately.
8. **Dropping approximate-oracle errors.** An inexact LMO changes the gap certificate and the descent recurrence.
9. **Using an unconstrained norm-gradient criterion.** Boundary stationary points may have nonzero gradient.
10. **Proving the stationarity equivalence with a supremum that is not attained.** Compactness and continuity justify a maximum.

## 6. Exercises

1. Prove that a local minimizer of differentiable \(f\) over convex \(\mathcal K\) satisfies (103.1).
2. Prove the equivalence between (103.1) and zero FW gap.
3. For the polynomial in §3.1, compute \(f'(x)\), verify the zero gap at \(0\), and find a feasible point with smaller objective.
4. Verify the Euclidean-ball gap formula in §3.2.
5. Derive the bound \(C_f\le LD^2\) from an \(L\)-Lipschitz gradient.
6. Starting from (103.6), prove the two decrease estimates (103.8) and (103.9).
7. Prove (103.10) by splitting on whether \(\delta_T\le C\).
8. Explain why the minimum-gap guarantee does not imply that every iterate’s gap decreases monotonically.
9. State the stationarity predicate using the normal cone and reconcile its sign with (103.1).
10. Formalize a finite run returning the smallest-gap iterate and its certificate.
11. Add an approximate LMO error \(\varepsilon_t\) and derive the modified one-step decrease.
12. Give an example of a stationary point that is not a local minimum, or explain why the example in §3.1 is a local but non-global minimum.

## 7. Chapter summary

For a nonconvex objective, the Frank–Wolfe gap is a constrained first-order stationarity measure, not an objective-error bound. It vanishes exactly when no feasible direction has a negative first-order derivative. This condition allows a nonzero ambient gradient at a boundary point and does not rule out better feasible points elsewhere.

A finite curvature bound gives a descent inequality without convexity. Choosing a step from the gap and summing decreases proves that the best FW gap among \(T\) iterates is \(O(T^{-1/2})\). In Lean, separate the variational stationarity equivalence, oracle optimality, segment curvature, per-step decrease, and finite-sum argument.

## Further reading

- Lacoste-Julien, [“Convergence Rate of Frank-Wolfe for Non-Convex Objectives”](https://arxiv.org/abs/1607.00345), for the affine-invariant curvature analysis and best-gap stationarity rate.
- Jaggi, [“Revisiting Frank–Wolfe: Projection-Free Sparse Convex Optimization”](https://proceedings.mlr.press/v28/jaggi13.html), for the curvature constant and convex duality-gap framework.
- Chapter 98 — Frank–Wolfe and Projection-Free Optimization, for convex objective-error guarantees and approximate linear oracles.

