# Chapter 91 — Smooth Convex Optimization and Gradient Descent

> **Audience.** This chapter assumes familiarity with convexity, gradients, and optimality certificates from Chapter 90. It develops the analysis behind gradient descent: the descent lemma, a finite-iteration error bound, and a linear rate under strong convexity.

An optimization algorithm produces a sequence of candidates. A proof about the algorithm must say what each step guarantees, how those guarantees compose, and which quantity actually converges. For gradient descent, the key input is not a mysterious property of the iteration. It is a quadratic upper bound on the objective, derived from a Lipschitz bound on its gradient.

We work first on a real Hilbert space, or a finite-dimensional Euclidean space, with an objective defined on the whole space. This choice keeps every gradient step feasible. A constrained method such as projected gradient descent needs a separate projection theorem and will be treated as a different interface. We also assume that a minimizer exists whenever a rate is measured relative to one; smoothness and convexity alone do not guarantee attainment of the infimum.

## Learning objectives

After this chapter, you should be able to:

- derive the descent lemma from a Lipschitz gradient bound;
- prove that a gradient step with step size \(1/L\) decreases the objective;
- obtain an \(O(1/k)\) objective-gap bound by telescoping a squared-distance estimate;
- derive a linear objective-gap rate for strongly convex objectives;
- separate smoothness, convexity, and minimizer existence in Lean theorem statements;
- formalize iterative algorithms using per-step invariants and finite sums.

## 1. Smoothness controls the error of a linear approximation

Let \(f:E\to\mathbb R\) be differentiable on a real inner-product space. Its gradient is \(L\)-Lipschitz when

\[
\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|
\qquad(x,y\in E),
\tag{91.1}
\]

for a constant \(L>0\). This bounds how quickly the first-order model changes. It does not say that \(f\) is convex: a smooth function may still have local maxima and saddle points.

The main consequence is the **descent lemma**:

\[
f(y)\le f(x)+\langle\nabla f(x),y-x\rangle
 +\frac{L}{2}\|y-x\|^2.
\tag{91.2}
\]

Compare this with Chapter 90's supporting inequality for a convex function, which gives a lower bound. Smoothness gives an upper bound on how far the function can rise above its tangent plane. Together, convexity and smoothness trap the objective between a supporting plane and a quadratic model.

To see (91.2), set \(d=y-x\) and restrict \(f\) to the segment \(\gamma(t)=x+td\). The fundamental theorem of calculus gives

\[
f(y)-f(x)=\int_0^1\langle\nabla f(x+td),d\rangle\,dt.
\]

Subtract the linear term at \(x\). By Cauchy–Schwarz and (91.1),

\[
\begin{aligned}
f(y)-f(x)-\langle\nabla f(x),d\rangle
&=\int_0^1\langle\nabla f(x+td)-\nabla f(x),d\rangle\,dt\\
&\le\int_0^1 Lt\|d\|^2\,dt\\
&=\frac{L}{2}\|d\|^2.
\end{aligned}
\]

The proof uses no convexity. It needs a derivative along the segment, an integral representation of the difference, the Lipschitz bound, and a scalar integral. This decomposition is useful in Lean: each analytical interface can be proved or imported independently, while the final inequality is an order calculation.

### 1.1 A second-derivative route

In a finite-dimensional space, one can instead assume a continuous Hessian and prove an operator bound

\[
0\preceq\nabla^2 f(x)\preceq L I
\qquad(x\in E).
\tag{91.3}
\]

The upper bound implies \(L\)-smoothness by integrating the Hessian along segments. The lower bound implies convexity. This route is attractive for quadratic and polynomial objectives, where Hessian calculations are explicit. The gradient-Lipschitz formulation is more general and avoids carrying a matrix order on Hessians through every optimization theorem.

Do not silently identify these two interfaces. A Hessian bound requires second derivatives and an order structure on self-adjoint operators. A Lipschitz-gradient hypothesis only requires first derivatives and a norm estimate. Prove a bridge lemma when a model naturally supplies Hessian information, then let the algorithm theorem consume the simpler gradient-Lipschitz contract.

## 2. The gradient step is a minimizer of the quadratic model

At \(x\), the right side of (91.2) is an upper model of \(f(y)\):

\[
m_x(y)=f(x)+\langle\nabla f(x),y-x\rangle
 +\frac{L}{2}\|y-x\|^2.
\tag{91.4}
\]

Completing the square shows that \(m_x\) has its unique minimum at

\[
y=x-\frac{1}{L}\nabla f(x).
\tag{91.5}
\]

Indeed, differentiating \(m_x\) in \(y\) gives \(\nabla f(x)+L(y-x)\), which vanishes at (91.5). The gradient step is therefore not an arbitrary move against the gradient: it minimizes a global quadratic upper bound on the objective.

Define the iterates

\[
x_{k+1}=x_k-\frac{1}{L}\nabla f(x_k).
\tag{91.6}
\]

Substitute \(y=x_{k+1}\) into the descent lemma. Since \(x_{k+1}-x_k=-\nabla f(x_k)/L\),

\[
f(x_{k+1})\le f(x_k)-\frac{1}{2L}\|\nabla f(x_k)\|^2.
\tag{91.7}
\]

Thus the objective is nonincreasing, and the decrease controls the squared gradient norm. Summing (91.7) for \(k=0,\ldots,N-1\) gives

\[
\frac{1}{2L}\sum_{k=0}^{N-1}\|\nabla f(x_k)\|^2
\le f(x_0)-f(x_N).
\tag{91.8}
\]

If \(f\) is bounded below by \(f_*\), then the sum on the left is bounded independently of \(N\). In particular, the average squared gradient norm among the first \(N\) iterates is at most \(2L(f(x_0)-f_*)/N\). This guarantees that some iterate has a small gradient. It does not by itself give a distance bound or a rate for the objective gap unless additional structure, such as convexity, is used.

### 2.1 Step sizes and backtracking

For a step size \(\eta\) with \(0<\eta\le1/L\), the same calculation gives

\[
f(x-\eta\nabla f(x))
\le f(x)-\eta\left(1-\frac{L\eta}{2}\right)\|\nabla f(x)\|^2.
\tag{91.9}
\]

The coefficient is positive for every \(0<\eta<2/L\); the more conservative range \(0<\eta\le1/L\) is convenient for the standard convex rate proof. If \(L\) is unknown, a backtracking procedure can test the quadratic inequality (91.2) at a trial step and reduce the step until the test succeeds. To verify backtracking, formalize the acceptance condition and prove that accepted steps preserve the descent inequality. The search history itself need not be part of the mathematical correctness theorem.

An accepted step is not automatically feasible for a constrained problem. If the domain is a convex set \(C\), (91.5) can leave \(C\). The projected method replaces it by the nearest point in \(C\), which requires existence and optimality properties for projections. Chapter 90's variational inequality already signals the extra work: at a constrained optimum, the gradient need not vanish.

## 3. Convexity turns descent into a finite-iteration error bound

Assume now that \(f\) is convex and has a minimizer \(x_*\), with \(f_*=f(x_*)\). Convexity gives the first-order inequality

\[
f(x_k)-f_*\le
\langle\nabla f(x_k),x_k-x_*\rangle.
\tag{91.10}
\]

Use the squared-distance identity for a gradient step:

\[
\|x_{k+1}-x_*\|^2
=\|x_k-x_*\|^2
-\frac{2}{L}\langle\nabla f(x_k),x_k-x_*\rangle
+\frac{1}{L^2}\|\nabla f(x_k)\|^2.
\]

Inequality (91.10) bounds the inner product below by the current objective gap. Inequality (91.7), rearranged, bounds the final squared-gradient term by \(2(f(x_k)-f(x_{k+1}))/L\). Combining the two bounds cancels the \(f(x_k)\) terms:

\[
\|x_{k+1}-x_*\|^2
\le\|x_k-x_*\|^2-\frac{2}{L}(f(x_{k+1})-f_*).
\tag{91.11}
\]

This is the key one-step invariant. Summing it over \(k=0,\ldots,N-1\) telescopes the distance terms:

\[
\frac{2}{L}\sum_{k=0}^{N-1}(f(x_{k+1})-f_*)
\le\|x_0-x_*\|^2.
\tag{91.12}
\]

The objective gaps are nonincreasing by (91.7), so each of the first \(N\) gaps is at least the last one. Consequently,

\[
f(x_N)-f_*
\le\frac{L\|x_0-x_*\|^2}{2N}
\qquad(N\ge1).
\tag{91.13}
\]

This is the \(O(1/N)\) rate for gradient descent on a smooth convex objective. The proof illustrates a pattern that appears throughout verified algorithms:

~~~text
one-step inequality
        │ sum over k = 0, ..., N−1
        ▼
telescoping potential + nonnegative error terms
        │ use monotonicity of the objective gaps
        ▼
explicit bound at the final iterate
~~~

The potential here is squared distance to an optimizer. The proof does not claim that \(x_N\) itself converges at rate \(1/N\); it bounds the objective gap. Convergence of iterates, convergence of gradient norms, and objective-value convergence are distinct conclusions and require distinct arguments.

### 3.1 A quadratic example with an exact trajectory

Let

\[
f(x)=\frac{a}{2}x^2,\qquad 0<a\le L.
\tag{91.14}
\]

The gradient is \(ax\), the unique minimizer is zero, and the gradient is \(L\)-Lipschitz because \(a\le L\). With step size \(1/L\),

\[
x_{k+1}=\left(1-\frac{a}{L}\right)x_k,\qquad
f(x_k)=\left(1-\frac{a}{L}\right)^{2k}f(x_0).
\tag{91.15}
\]

The actual objective gap decays geometrically, much faster than the general convex guarantee (91.13) when \(a>0\). The general theorem does not exploit a positive lower curvature bound; strong convexity will do so in the next section. If \(a=L\), this particular quadratic reaches its minimizer in one step. This is a useful test case for an implementation, but it should not be mistaken for the worst-case behavior of all smooth convex objectives.

### 3.2 Two curvatures and the condition number

On \(\mathbb R^2\), consider

\[
f(u,v)=\frac12(\mu u^2+L v^2),\qquad 0<\mu\le L.
\tag{91.16}
\]

The eigen-directions have different curvatures. A gradient step with step size \(1/L\) gives

\[
u_{k+1}=\left(1-\frac{\mu}{L}\right)u_k,\qquad
v_{k+1}=0.
\tag{91.17}
\]

The direction with curvature \(L\) is eliminated in one step, while the flatter direction contracts by \(1-\mu/L\). For \(k\ge1\), the objective gap is exactly

\[
f(u_k,v_k)-f(0,0)
=\frac{\mu}{2}\left(1-\frac{\mu}{L}\right)^{2k}u_0^2.
\tag{91.18}
\]

When \(L/\mu\) is large, the factor \(1-\mu/L\) is close to one, so progress in the flat direction is slow. This example gives a geometric interpretation of the condition number and shows why an algorithm's rate depends on the relative scale of its steepest and flattest directions.

## 4. Strong convexity gives a linear objective-gap rate

Suppose \(f\) is \(\mu\)-strongly convex and its gradient is \(L\)-Lipschitz, with \(0<\mu\le L\). Strong convexity implies the gradient-dominance inequality

\[
\|\nabla f(x)\|^2\ge2\mu(f(x)-f_*).
\tag{91.19}
\]

To derive it, use the strong supporting inequality from Chapter 90 with competitor \(x_*\):

\[
f_*\ge f(x)+\langle\nabla f(x),x_*-x\rangle
+\frac{\mu}{2}\|x_*-x\|^2.
\]

Rearrange and maximize the right-hand expression over the displacement \(x-x_*\). The scalar inequality

\[
\langle g,d\rangle-\frac{\mu}{2}\|d\|^2
\le\frac{\|g\|^2}{2\mu}
\]

then yields \(f(x)-f_*\le\|\nabla f(x)\|^2/(2\mu)\), which is equivalent to (91.19).

Combining (91.7) and (91.19) gives

\[
f(x_{k+1})-f_*
\le\left(1-\frac{\mu}{L}\right)(f(x_k)-f_*).
\tag{91.20}
\]

Iterating,

\[
f(x_N)-f_*
\le\left(1-\frac{\mu}{L}\right)^N(f(x_0)-f_*).
\tag{91.21}
\]

The rate is geometric. When \(\mu/L\) is small, progress is slower; when the curvature lower bound is close to the smoothness upper bound, the factor is small. The ratio \(L/\mu\) is the condition number in this setting. Preconditioning aims to improve this ratio by changing coordinates or the geometry used to measure steps.

Strong convexity also yields a distance guarantee from the objective gap:

\[
\|x_N-x_*\|^2\le\frac{2}{\mu}(f(x_N)-f_*).
\tag{91.22}
\]

Combining it with (91.21) yields a geometric squared-distance bound. Notice the logical order: the algorithm theorem first proves a function-value estimate; strong convexity converts that estimate into distance. This modular route avoids proving a direct contraction theorem for the gradient map, which may need a sharper smoothness argument.

## 5. Lean interfaces for gradient descent

### 5.1 State the analytic contracts separately

A useful smoothness predicate records global differentiability and the gradient Lipschitz bound:

~~~lean
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def GradientLipschitz (f : E → ℝ) (L : ℝ) : Prop :=
  0 < L ∧
    (∀ x, DifferentiableAt ℝ f x) ∧
    ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
~~~

The exact imports and namespace should be checked against the Mathlib version pinned by the project. Mathlib's gradient interface connects gradients to Fréchet derivatives in complete inner-product spaces; for a proof that does not need a gradient vector, state the derivative theorem using a continuous linear map instead. The chapter uses the predicate above to make the mathematical contract visible, not to prescribe a universal library definition.

Keep convexity in a separate hypothesis. Smoothness supports (91.2); convexity supports (91.10); strong convexity supports (91.19). A theorem that packages all three conditions into one opaque predicate is harder to reuse. Prefer small structures only when a downstream API repeatedly needs the combined data.

### 5.2 Define one step before defining the sequence

The deterministic update can be stated independently:

~~~lean
noncomputable def gdStep (L : ℝ) (f : E → ℝ) (x : E) : E :=
  x - (1 / L) • gradient f x
~~~

First prove local lemmas about this step: the objective decrease (91.7), the squared-distance estimate (91.11), and the strong-convexity gap recurrence (91.20). Then define iterates recursively or by repeated application of gdStep. This keeps the analytical proof independent of the chosen sequence encoding.

If using a recursive sequence, align the index carefully: \(x_0\) is the initial point, and each application of gdStep produces \(x_{k+1}\). The finite sum in (91.12) contains gaps at indices \(1,\ldots,N\), not \(0,\ldots,N-1\). Writing down the index map before invoking finite-sum lemmas prevents common off-by-one errors.

### 5.3 Prove the rate with a potential and a telescope

The Lean proof of (91.12) should follow its mathematics:

1. prove the one-step distance inequality for an arbitrary index \(k\);
2. sum the inequalities over a finite interval;
3. cancel adjacent squared-distance terms;
4. use nonnegativity of the final squared distance;
5. use monotonicity of the objective gaps to bound the last gap by their average.

The finite-sum step is often the most syntactic part. A dedicated lemma for telescoping a sequence difference keeps rewriting under control. Do not ask an arithmetic solver to discover the telescope; expose it as an algebraic identity and then use order reasoning for the nonnegative terms.

For (91.21), a simple induction on \(N\) applies the recurrence (91.20). Keep \(1-\mu/L\) nonnegative; this follows from \(0<\mu\le L\). If an exponent is cast between natural and real numbers, isolate that cast once in the induction lemma rather than mixing coercion rewriting with the analytic step.

### 5.4 Abstract the proof over the space when it pays off

The descent inequality uses an inner product, a norm, and a complete space for the global gradient interface. Some intermediate estimates only require a normed vector space and a Fréchet derivative. Do not force every theorem into a Hilbert-space typeclass merely because the final algorithm uses gradients. A derivative-valued descent lemma can support Banach-space applications; a gradient-specific corollary can then use the inner product representation.

Conversely, fully general scalar fields and abstract modules can make this chapter's order and calculus hypotheses difficult to read. The intended application is real optimization, so state the optimization results over \(\mathbb R\) and generalize only where it removes real duplication. This is the same abstraction discipline used elsewhere in the book: generalize to the reusable mathematical interface, not to every typeclass combination available.

## 6. Common failure modes

1. **Using convexity to justify the descent lemma.** The descent lemma follows from gradient Lipschitzness; convexity enters the rate proof later.
2. **Using smoothness to claim a global minimum exists.** Add an attainment hypothesis or prove existence from compactness or coercivity.
3. **Applying the unconstrained update to a constrained problem.** A gradient step can leave the feasible set. Use a projected method with its own projection theorem.
4. **Confusing objective convergence with iterate convergence.** Bound the quantity stated by the theorem; do not infer the others without a separate argument.
5. **Claiming a gradient-norm bound from only convexity.** The descent sum gives a small gradient somewhere if the objective is bounded below, but a function-gap rate needs a minimizer and convexity.
6. **Dropping the step-size condition.** The coefficient in (91.9) must be nonnegative for monotone decrease.
7. **Summing without tracking indices.** State which iterate each gap belongs to before telescoping.
8. **Using a finite-sum tactic to invent the invariant.** Prove the one-step estimate first; the sum should reveal a prepared telescope.
9. **Asserting a distance contraction from the objective recurrence.** Convert objective gap to distance using strong convexity, or separately prove a gradient-map contraction under suitable hypotheses.
10. **Treating a quadratic example as representative of every model.** The exact trajectory is a check case, not a general convergence proof.

## 7. Exercises

1. Prove the descent lemma by integrating the directional derivative along the segment from \(x\) to \(y\).
2. Starting from (91.2), derive (91.9) for a step size \(0<\eta\le1/L\).
3. Let \(f(x)=\frac{a}{2}x^2\) with \(0<a\le L\). Compute the gradient-descent iterates and objective gap exactly.
4. For the two-dimensional example, compute the Hessian eigenvalues and verify the strong-convexity and smoothness constants.
5. Verify (91.11) by expanding the squared norm and substituting the convexity and descent inequalities.
6. Show that the average of the first \(N\) squared gradient norms is bounded by \(2L(f(x_0)-f_*)/N\). Explain why this does not imply every one of those norms is small.
7. Derive (91.19) from the strong supporting inequality and the inner-product Cauchy–Schwarz inequality.
8. Formalize GradientLipschitz and gdStep. Prove a one-step descent theorem before defining an iterative sequence.
9. Write a finite-sum lemma that turns inequalities \(V_{k+1}\le V_k-c\,a_{k+1}\) into a bound on \(\sum_{k=0}^{N-1}a_{k+1}\).
10. Construct a smooth convex function on an open interval whose infimum is not attained. Which hypothesis of the rate theorem fails?
11. Explain how the proof changes if the update is projected onto a closed convex set.

## 8. Chapter summary

A Lipschitz gradient yields a quadratic upper model of the objective. The gradient step minimizes that model and therefore decreases the objective by an amount controlled by the squared gradient norm. Convexity adds a squared-distance potential relative to an optimizer; summing its one-step inequality proves an \(O(1/N)\) objective-gap bound. Strong convexity converts gradient norm into objective gap and upgrades the rate to geometric convergence.

The Lean development should mirror this dependency chain: differentiability and smoothness give the descent lemma; convexity gives the distance estimate; finite sums telescope; strong convexity supplies the final error conversion. Keeping those interfaces separate makes the algorithm theorem easier to inspect and reuse.

## Further reading

- Mathlib's [gradient interface](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Gradient/Basic.lean), including the relation between gradients and Fréchet derivatives.
- Mathlib's [convex-function interface](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Function.html) for convex functions and their chord inequalities.
- Nesterov, *Introductory Lectures on Convex Optimization*, for smoothness inequalities, gradient methods, and condition-number-dependent rates.
- Bubeck, *Convex Optimization: Algorithms and Complexity*, for algorithmic convergence proofs organized around potentials and one-step inequalities.
