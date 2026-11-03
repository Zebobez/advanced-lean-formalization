# Chapter 92 — Projected Gradient and Proximal Methods

> **Audience.** This chapter assumes the convexity and smooth-gradient results from Chapters 90–91. It develops constrained gradient descent through Hilbert projection, then extends the same proof pattern to composite objectives with nonsmooth convex terms.

An unconstrained gradient step can leave a feasible set. Clipping the result back into the set is not an implementation detail: the projection has an optimality condition, and that condition is what replaces the zero-gradient equation at a constrained optimum. The same structure appears in proximal algorithms, where projection is one example of a more general operation that handles a nonsmooth term exactly.

We develop three layers. First, the Hilbert projection theorem gives a unique nearest feasible point and a variational inequality. Second, projected gradient descent minimizes a quadratic model over the feasible set and inherits a telescoping convergence proof. Third, the proximal map minimizes a quadratic-regularized nonsmooth objective, extending the method from constrained smooth optimization to composite optimization.

## Learning objectives

After this chapter, you should be able to:

- characterize projection onto a closed convex set by an inner-product inequality;
- derive the projected-gradient update as a constrained quadratic minimizer;
- prove a one-step three-point inequality and telescope it into an objective-gap bound;
- recognize projection as the proximal map of a set indicator;
- derive soft thresholding as the proximal map of the absolute-value penalty;
- organize Lean developments around existence, characterization, and algorithmic use of projections.

## 1. Projection onto a closed convex set

Let \(E\) be a real Hilbert space and let \(C\subseteq E\) be nonempty, closed, and convex. For every \(z\in E\), there is a unique point in \(C\) closest to \(z\). Write this point as \(P_C(z)\):

\[
P_C(z)\in C,\qquad
\|z-P_C(z)\|=\inf_{y\in C}\|z-y\|.
\tag{92.1}
\]

Existence uses completeness and convexity; uniqueness uses the strict convexity of the squared norm in a Hilbert space. A closed set alone can have multiple nearest points, and a nonclosed set may have an infimum distance that is not attained. State the hypotheses that supply existence and uniqueness rather than treating projection as a total operation on arbitrary sets.

The nearest-point property is equivalent to the variational inequality

\[
\langle z-P_C(z),y-P_C(z)\rangle\le0
\qquad(y\in C).
\tag{92.2}
\]

To obtain the necessary condition, move from \(p=P_C(z)\) toward any feasible \(y\). The segment \(p+t(y-p)\) stays in \(C\). Minimality of \(p\) means that the squared distance from \(z\) cannot decrease as \(t\) increases from zero. Differentiating this squared distance at zero gives (92.2). Conversely, expand the square:

\[
\|z-y\|^2
=\|z-p\|^2+\|y-p\|^2
-2\langle z-p,y-p\rangle.
\]

By (92.2), the last term is nonnegative, so \(\|z-y\|^2\ge\|z-p\|^2\). This proves that \(p\) is nearest. If two points both satisfy the variational inequality, apply each inequality to the other point and add; the squared distance between them must be zero.

The projection is firmly nonexpansive:

\[
\|P_C(u)-P_C(v)\|^2
\le\langle P_C(u)-P_C(v),u-v\rangle.
\tag{92.3}
\]

Indeed, apply (92.2) twice, using \(P_C(v)\) as the comparison point for the projection of \(u\), and \(P_C(u)\) for the projection of \(v\). Adding gives (92.3). Cauchy–Schwarz then implies the simpler nonexpansive bound \(\|P_C(u)-P_C(v)\|\le\|u-v\|\). Firm nonexpansiveness is stronger and often the useful interface for convergence proofs.

### 1.1 A one-dimensional projection

For \(C=[0,1]\subseteq\mathbb R\), projection is clipping:

\[
P_C(z)=\min(\max(z,0),1).
\tag{92.4}
\]

If \(z<0\), the nearest feasible point is \(0\); if \(0\le z\le1\), it is \(z\); if \(z>1\), it is \(1\). The three cases also make the sign in (92.2) concrete. At \(z>1\), the residual \(z-P_C(z)\) is positive while every feasible displacement from \(1\) is nonpositive, so their product is nonpositive.

## 2. Projected gradient is constrained model minimization

Let \(f:E\to\mathbb R\) be convex with an \(L\)-Lipschitz gradient, and suppose we minimize it over \(C\). At a feasible point \(x_k\), form the quadratic upper model from Chapter 91:

\[
m_{x_k}(y)=f(x_k)+\langle\nabla f(x_k),y-x_k\rangle
+\frac{L}{2}\|y-x_k\|^2.
\tag{92.5}
\]

The projected step minimizes this model over the feasible set:

\[
x_{k+1}=\mathop{\rm argmin}_{y\in C}m_{x_k}(y)
=P_C\left(x_k-\frac{1}{L}\nabla f(x_k)\right).
\tag{92.6}
\]

The equality follows by completing the square. Since \(x_k\in C\), the projection is well-defined and the new iterate is feasible. By the descent lemma, \(f(y)\le m_{x_k}(y)\) for all \(y\). Since \(x_{k+1}\) minimizes \(m_{x_k}\) over \(C\),

\[
f(x_{k+1})\le m_{x_k}(x_{k+1})
\le m_{x_k}(x_k)=f(x_k).
\tag{92.7}
\]

Thus every step is feasible and the objective does not increase.

The first-order condition for the projection gives, for every \(y\in C\),

\[
\left\langle\nabla f(x_k)+L(x_{k+1}-x_k),
y-x_{k+1}\right\rangle\ge0.
\tag{92.8}
\]

This is the constrained stationarity condition for the quadratic model. If \(x_k\) is already a minimizer of \(f\) on \(C\), its gradient need not vanish; instead, the negative gradient is blocked by the normal cone, exactly as in Chapter 90.

### 2.1 A three-point inequality

The central estimate compares the new iterate to any feasible reference point \(y\in C\):

\[
f(x_{k+1})-f(y)
\le\frac{L}{2}\left(
\|x_k-y\|^2-\|x_{k+1}-y\|^2
\right).
\tag{92.9}
\]

For the proof, write \(p=x_{k+1}\), \(x=x_k\), and \(g=\nabla f(x_k)\). Smoothness bounds \(f(p)\) above by \(f(x)+\langle g,p-x\rangle+(L/2)\|p-x\|^2\). Convexity bounds \(f(y)\) below by \(f(x)+\langle g,y-x\rangle\). Subtracting gives

\[
f(p)-f(y)
\le\langle g,p-y\rangle+\frac L2\|p-x\|^2.
\]

The projection optimality condition (92.8) bounds the first term by
\(-L\langle p-x,p-y\rangle\). The identity

\[
2\langle p-x,p-y\rangle
=\|x-p\|^2+\|p-y\|^2-\|x-y\|^2.
\tag{92.10}
\]

This identity cancels the positive squared-step term exactly and yields (92.9). The three-point bound is the key interface: it records progress toward \(y\) as a decrease in squared distance.

### 2.2 Convergence rate on a convex feasible set

Suppose \(x_*\in C\) minimizes \(f\) over \(C\). Put \(y=x_*\) in (92.9):

\[
f(x_{k+1})-f(x_*)
\le\frac L2\left(
\|x_k-x_*\|^2-\|x_{k+1}-x_*\|^2
\right).
\tag{92.11}
\]

Summing from \(k=0\) to \(N-1\) telescopes the squared distances:

\[
\sum_{k=0}^{N-1}(f(x_{k+1})-f(x_*))
\le\frac L2\|x_0-x_*\|^2.
\tag{92.12}
\]

The objective is nonincreasing by (92.7), so each gap on the left is at least the final gap. Therefore

\[
f(x_N)-f(x_*)
\le\frac{L\|x_0-x_*\|^2}{2N}
\qquad(N\ge1).
\tag{92.13}
\]

The same \(O(1/N)\) guarantee from Chapter 91 holds under a convex constraint. The proof's only new ingredient is the projection variational inequality. This is a useful formalization pattern: keep the analytic estimate from the unconstrained case, then replace the step lemma with a constrained three-point inequality.

### 2.3 The projected-gradient mapping

The projection step also gives a first-order stopping certificate. For a fixed step size \(\eta>0\), define

\[
G_\eta(x)=\frac{1}{\eta}\left(x-P_C(x-\eta\nabla f(x))\right).
\]

If \(G_\eta(x)=0\), then \(x=P_C(x-\eta\nabla f(x))\). Applying the projection inequality (92.2) with \(z=x-\eta\nabla f(x)\) and \(p=x\) gives

\[
\langle\nabla f(x),y-x\rangle\ge0\qquad(y\in C).
\]

For convex \(f\), Chapter 90 shows this is equivalent to global constrained optimality. Conversely, if \(x\) is optimal, its variational inequality makes \(x\) the projection of \(x-\eta\nabla f(x)\), so the mapping vanishes. Thus \(G_\eta(x)=0\) exactly characterizes constrained minimizers.

The norm of this mapping is a natural approximate-stationarity measure. Let \(p=P_C(x-\eta\nabla f(x))\). Projection optimality with \(y=x\), followed by the descent lemma, gives

\[
f(x)-f(p)\ge\left(\frac{1}{\eta}-\frac L2\right)\|p-x\|^2.
\]

When \(\eta=1/L\), this becomes \(f(x)-f(p)\ge(\eta/2)\|G_\eta(x)\|^2\). Therefore a small projected-gradient mapping guarantees a small decrease in one step. It does not by itself certify a small objective gap unless further curvature information is available. This distinction matters when an implementation uses a residual norm as its stopping rule.

### 2.4 A boundary optimum

Minimize \(f(x)=\tfrac12(x-2)^2\) over \(C=[0,1]\). Starting from \(x_0=0.2\) with \(L=1\), the raw gradient step is

\[
x_0-f'(x_0)=0.2-(-1.8)=2.
\]

Projecting gives \(x_1=P_C(2)=1\), the constrained minimizer. At the boundary \(x_*=1\), \(f'(1)=-1\) is not zero. For every feasible \(y\le1\),

\[
f'(1)(y-1)=-(y-1)\ge0,
\]

which is the variational inequality. The projection turns the infeasible descent direction into a feasible step and the first-order condition certifies the boundary solution.

## 3. Proximal maps and composite objectives

Let \(g:E\to\mathbb R\cup\{+\infty\}\) be a proper lower semicontinuous convex function. Its proximal map at parameter \(\eta>0\) is the unique minimizer

\[
\operatorname{prox}_{\eta g}(z)
=\mathop{\rm argmin}_{u\in E}
\left(g(u)+\frac{1}{2\eta}\|u-z\|^2\right).
\tag{92.14}
\]

The quadratic term makes the objective strongly convex, giving uniqueness; lower semicontinuity and coercivity supply existence in the usual Hilbert-space setting. The minimizer is characterized by

\[
\frac{z-\operatorname{prox}_{\eta g}(z)}{\eta}
\in\partial g(\operatorname{prox}_{\eta g}(z)).
\tag{92.15}
\]

This condition says that the quadratic force toward \(z\) is balanced by a subgradient of \(g\). It is the nonsmooth counterpart of setting the derivative of a smooth objective to zero.

Now minimize a composite objective

\[
F(x)=f(x)+g(x),
\tag{92.16}
\]

where \(f\) is convex and smooth and \(g\) is convex but may be nonsmooth. Proximal gradient takes the smooth gradient step, then applies the proximal map:

\[
x_{k+1}=\operatorname{prox}_{\eta g}
\left(x_k-\eta\nabla f(x_k)\right).
\tag{92.17}
\]

The point \(x_{k+1}\) minimizes the local model

\[
g(y)+\langle\nabla f(x_k),y-x_k\rangle
+\frac{1}{2\eta}\|y-x_k\|^2.
\tag{92.18}
\]

When \(0<\eta\le1/L\), this model majorizes \(F\): the smooth part is controlled by the descent lemma and \(1/(2\eta)\ge L/2\). Hence proximal gradient decreases \(F\). A strong-convexity argument for the model yields the three-point inequality

\[
F(x_{k+1})-F(y)
\le\frac{1}{2\eta}\left(
\|x_k-y\|^2-\|x_{k+1}-y\|^2
\right)
 \qquad(F(y)<+\infty).
\tag{92.19}
\]

The derivation mirrors the projected proof. The proximal minimization supplies a comparison with \(y\); smoothness upper-bounds \(f(x_{k+1})\); convexity lower-bounds \(f(y)\). With \(y=x_*\), where \(x_*\) minimizes \(F\), telescoping gives

\[
F(x_N)-F(x_*)\le
\frac{\|x_0-x_*\|^2}{2\eta N}.
\tag{92.20}
\]

At \(\eta=1/L\), this agrees with the projected rate. Projection is therefore not an isolated trick: it is the proximal method for a particular nonsmooth penalty.

### 3.1 Constraints as an indicator function

Define the extended-real indicator of \(C\) by

\[
\iota_C(x)=
\begin{cases}
0,&x\in C,\\
+\infty,&x\notin C.
\end{cases}
\tag{92.21}
\]

Then minimizing \(f\) over \(C\) is the same as minimizing \(f+\iota_C\) over all of \(E\). Its proximal map is exactly projection:

\[
\operatorname{prox}_{\eta\iota_C}(z)=P_C(z).
\tag{92.22}
\]

The indicator formalism unifies constraints and nonsmooth penalties, but it introduces extended-real-valued functions and subdifferentials. A small development can keep the projected method stated directly on \(C\); a reusable convex-analysis library may prefer the composite formulation.

### 3.2 Soft thresholding

Take \(E=\mathbb R\) and \(g(u)=\lambda|u|\), where \(\lambda>0\). The proximal problem is

\[
\min_u\left(\lambda|u|+\frac{1}{2\eta}(u-z)^2\right).
\]

If \(u>0\), stationarity gives \(u=z-\eta\lambda\), which is valid when \(z>\eta\lambda\). If \(u<0\), it gives \(u=z+\eta\lambda\), valid when \(z<-\eta\lambda\). Otherwise the subgradient interval of \(|u|\) at zero contains \(z/(\eta\lambda)\), and the minimizer is zero. Combining the cases,

\[
\operatorname{prox}_{\eta\lambda|\cdot|}(z)
=\operatorname{sign}(z)\max(|z|-\eta\lambda,0).
\tag{92.23}
\]

This soft-thresholding rule is the basic step in sparse regression algorithms. It sets small coordinates exactly to zero, a behavior ordinary gradient descent on a smooth approximation would not reproduce exactly.

## 4. Lean proof architecture

### 4.1 Separate existence from characterization

The projection development has two logically distinct theorems:

1. a Hilbert projection theorem: a nonempty complete convex set has a nearest point to any ambient point;
2. a variational characterization: a feasible point is nearest exactly when it satisfies the inner-product inequality.

Mathlib's current Hilbert projection development exposes these interfaces as **exists_norm_eq_iInf_of_complete_convex** and **norm_eq_iInf_iff_real_inner_le_zero**. The first theorem asks for completeness of the set itself, not merely an unqualified label saying that the set is closed. In a complete ambient Hilbert space, closedness supplies that set completeness. The second theorem is the computationally useful certificate: once a candidate is supplied, verify feasibility and one scalar inequality for every competitor.

Avoid identifying this theorem with **Submodule.orthogonalProjection**. Orthogonal projection onto a subspace is a special linear construction. Projection onto a general convex set is nonlinear, though still nonexpansive. The mathematical object and Lean type should reflect that distinction.

### 4.2 Package a candidate certificate

For an algorithm step, one rarely needs to unfold the infimum characterization. A local certificate can package:

- \(p\in C\);
- the projection variational inequality for \(z-p\);
- optionally, a distance-minimality result derived from that inequality.

One can make that certificate the central local predicate:

~~~lean
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsProjectionCandidate (C : Set E) (z p : E) : Prop :=
  p ∈ C ∧ ∀ y ∈ C, inner ℝ (z - p) (y - p) ≤ 0
~~~

The ambient completeness assumption is not needed to verify a proposed candidate; it is needed to produce one for every \(z\). This distinction keeps the checker theorem applicable to closed forms, while a separate existence theorem can invoke the Hilbert projection result. Uniqueness follows from the certificate alone, by comparing two candidates with each other and using positive definiteness of the inner product.

Then prove a generic lemma: every candidate satisfying the certificate is the unique projection. The optimizer can compute a candidate by a closed form, numerical method, or recursive routine; Lean checks the certificate. This mirrors Chapter 89's division between numerical discovery and a small verifiable witness.

The following interface packages the candidate certificate and checks it against Mathlib’s convex projection characterization. The nearest-point equivalence needs convexity. Uniqueness follows from the two candidate inequalities and positive definiteness of the inner product, so the uniqueness theorem itself does not assume convexity.

```lean
import Book.Models.FiniteOptimization

open Book.Models.FiniteOptimization

theorem projected_step_keeps_first_feasible : projectedStep first = first := by decide

theorem projected_step_reaches_minimum_from_middle : projectedStep middle = last := by decide

def IsProjectionCandidate {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (z p : E) : Prop :=
  p ∈ C ∧ ∀ y ∈ C, inner ℝ (z - p) (y - p) ≤ 0

theorem projection_candidate_is_nearest
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) {z p : E}
    (hp : IsProjectionCandidate C z p) :
    ‖z - p‖ = ⨅ y : C, ‖z - y‖ := by
  exact (norm_eq_iInf_iff_real_inner_le_zero hC hp.1).2 hp.2

theorem projection_candidate_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {z p q : E}
    (hp : IsProjectionCandidate C z p)
    (hq : IsProjectionCandidate C z q) :
    p = q := by
  have h₁ := hp.2 q hq.1
  have h₂ := hq.2 p hp.1
  have hidentity :
      inner ℝ (q - p) (q - p) =
        inner ℝ (z - p) (q - p) + inner ℝ (z - q) (p - q) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hinner : inner ℝ (q - p) (q - p) ≤ 0 := by
    rw [hidentity]
    exact add_nonpos h₁ h₂
  have hnorm_sq : ‖q - p‖ ^ 2 ≤ 0 := by
    rwa [← real_inner_self_eq_norm_sq]
  have hnorm_zero : ‖q - p‖ = 0 := by
    nlinarith [sq_nonneg (‖q - p‖)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)).symm
```

### 4.3 Represent proximal operators by their minimization property

For a general extended-real-valued \(g\), defining the proximal map as a function requires existence for every input and a choice of a minimizer. A theorem about an arbitrary minimizer can often avoid this choice:

- assume \(p\) minimizes the regularized objective;
- derive its subgradient or three-point inequality;
- apply the result to any chosen proximal implementation.

If a project does define a proximal function, prove its existence, uniqueness, and optimality characterization once, then use only the characterization in algorithm proofs. Be explicit about properness, lower semicontinuity, convexity, and the positive parameter. Omitting any of these can invalidate existence or uniqueness.

### 4.4 Keep the telescope index-visible

For projected gradient, prove (92.11) for an arbitrary step, sum over the finite interval \(0\le k<N\), and only then use monotonicity. For proximal gradient, do the same with (92.19). A shared finite-sum lemma can handle both once their one-step statements have the same shape. This is a valuable abstraction: the algorithm-specific proof establishes the inequality; the generic theorem turns it into a rate.

## 5. Common failure modes

1. **Projecting onto a set without proving existence.** Use nonemptiness, convexity, and completeness in a Hilbert space.
2. **Assuming closedness alone gives uniqueness in every normed space.** The Hilbert projection theorem uses inner-product geometry.
3. **Confusing subspace projection with convex-set projection.** General convex projection is not a linear map.
4. **Using the wrong variational-inequality sign.** With residual \(z-p\) and displacement \(y-p\), their inner product is nonpositive.
5. **Dropping feasibility of the reference point.** The projection comparison and constrained optimality condition require \(y\in C\).
6. **Taking a raw gradient step under constraints.** It may be infeasible; projection is part of the mathematical update.
7. **Using a subgradient as if it were a derivative.** At a nonsmooth point, use the defining inequality or subdifferential characterization.
8. **Defining a proximal function before proving minimizer existence.** A minimization expression is not automatically a total function.
9. **Claiming a rate without a minimizer.** State attainment or prove it independently.
10. **Using an unverified proximal formula.** Prove the candidate minimizes the regularized objective, including boundary cases such as the threshold in soft shrinkage.

## 6. Exercises

1. Prove the variational characterization (92.2) in both directions.
2. Derive firm nonexpansiveness (92.3) by adding the two projection inequalities.
3. Verify the clipping formula (92.4) and its variational inequality in all three regions.
4. Starting from (92.8), prove the three-point estimate (92.9), using the squared-norm identity (92.10).
5. Telescope (92.11) and use monotonicity to prove (92.13).
6. For \(f(x)=\tfrac12(x-2)^2\) on \([0,1]\), verify each step from \(x_0=0.2\) and prove \(x_*=1\) satisfies the constrained optimality condition.
7. Derive the subgradient condition (92.15) for a proximal minimizer.
8. Prove the soft-thresholding formula (92.23) by separating \(u>0\), \(u<0\), and \(u=0\).
9. Show that the proximal map of the indicator function of \(C\) is \(P_C\).
10. Design a Lean interface for an arbitrary projection candidate and prove uniqueness from its variational inequality.
11. State a generic finite-sum theorem that converts a three-point inequality into an \(O(1/N)\) objective bound.

## 7. Chapter summary

Projection onto a nonempty closed convex subset of a Hilbert space is characterized by an inner-product inequality. That inequality makes projected gradient a constrained minimizer of a quadratic upper model and yields a three-point estimate that telescopes to an \(O(1/N)\) objective-gap bound. Proximal gradient repeats the same design for a composite objective \(f+g\), while projection appears as the proximal map of an indicator function.

In Lean, separate the existence theorem for the projection from the certificate that characterizes it. Prove algorithmic one-step inequalities independently of sequence encodings, then reuse a generic finite-sum telescope. For proximal methods, treat minimizer existence and the optimality condition as explicit interfaces, especially when the objective is extended-real-valued.

## Further reading

- Mathlib's [Hilbert projection theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Minimal.html), including existence of nearest points and the inner-product characterization.
- Mathlib's [convex-set interface](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Convex/Basic.lean) for segment membership and convexity lemmas.
- Parikh and Boyd, “Proximal Algorithms,” for a broad treatment of proximal maps and composite optimization.
- Bauschke and Combettes, *Convex Analysis and Monotone Operator Theory in Hilbert Spaces*, for projection, resolvents, and firmly nonexpansive operators.
