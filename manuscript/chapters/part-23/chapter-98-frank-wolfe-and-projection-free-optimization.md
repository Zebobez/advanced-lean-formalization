# Chapter 98 — Frank–Wolfe and Projection-Free Optimization

> **Audience.** This chapter assumes the convexity, smoothness, and optimality tools from Chapters 90–94. It develops the conditional-gradient method, which replaces a projection or proximal solve with a linear optimization oracle over the feasible set.

Projection can be the expensive part of a constrained optimization algorithm. A set may be easy to optimize a linear function over, yet difficult to project onto in Euclidean distance. Frank–Wolfe methods exploit this difference. Each iteration solves a linear problem, then moves toward its solution by a convex combination. The iterate remains feasible without a projection.

The proof has three layers: a linear-oracle certificate gives a computable gap; curvature controls the objective change along a feasible segment; a recurrence converts the gap into an \(O(1/T)\) objective bound. The algorithm also has a sparse representation when the feasible set is a convex hull of atoms, because each step adds at most one new atom.

## Learning objectives

After this chapter, you should be able to:

- state the linear minimization oracle certificate and derive the Frank–Wolfe gap;
- prove that the duality gap upper-bounds the objective suboptimality;
- define the curvature constant and derive the primal \(O(1/T)\) rate;
- formalize exact and approximate linear-oracle steps;
- explain why convex-combination updates preserve feasibility and can preserve sparsity;
- design Lean interfaces for the oracle, curvature inequality, and finite recurrence separately.

## 1. Replace projection with a linear oracle

Let \(E\) be a finite-dimensional real inner-product space, let \(X\subset E\) be nonempty, compact, and convex, and let \(f:X\to\mathbb R\) be differentiable and convex. At the current point \(x_t\), compute a minimizer of the linearization:

\[
s_t\in\arg\min_{s\in X}\langle\nabla f(x_t),s\rangle.
\tag{98.1}
\]

Then update toward this point:

\[
x_{t+1}=x_t+\gamma_t(s_t-x_t)
=(1-\gamma_t)x_t+\gamma_t s_t,
\qquad 0\le\gamma_t\le1.
\tag{98.2}
\]

Convexity of \(X\) guarantees \(x_{t+1}\in X\). The method never asks for the projection of an arbitrary point back to \(X\). Its main computational primitive is a linear minimization oracle (LMO), which accepts a vector \(g\) and returns \(s\in X\) minimizing \(\langle g,s\rangle\).

The two subproblems encode different geometry. Projection solves \(\arg\min_{x\in X}\|z-x\|_2^2\); the LMO solves \(\arg\min_{s\in X}\langle g,s\rangle\). A projection often returns a point with many active coordinates, while an LMO may return a single atom. Neither oracle is automatically cheap, so algorithm design begins by comparing the actual operations required by the feasible set.

This distinction matters for complicated feasible sets. For a probability simplex, the LMO is a minimum over coordinates. For a nuclear-norm ball, it can be computed from a leading singular-vector pair, while Euclidean projection may require many singular values. The LMO need not be cheap for every set; the method is useful when its linear subproblem is simpler than projection.

## 2. The Frank–Wolfe gap is an optimality certificate

Define the gap at \(x\in X\) by

\[
g_{\mathrm{FW}}(x)
=\max_{s\in X}\langle\nabla f(x),x-s\rangle.
\tag{98.3}
\]

For an exact oracle solution \(s(x)\), this maximum is attained at that solution:

\[
g_{\mathrm{FW}}(x)
=\langle\nabla f(x),x-s(x)\rangle\ge0.
\tag{98.4}
\]

Let \(x^\star\) be a minimizer of \(f\) on \(X\). Convexity gives

\[
f(x)-f(x^\star)
\le\langle\nabla f(x),x-x^\star\rangle
\le g_{\mathrm{FW}}(x).
\tag{98.5}
\]

Thus a small exact gap certifies a small primal error without knowing \(f(x^\star)\). It is a stopping certificate, though the gap itself need not decrease monotonically at every iteration.

If \(g_{\mathrm{FW}}(x)=0\), then \(\langle\nabla f(x),u-x\rangle\ge0\) for every \(u\in X\). The convex subgradient inequality gives \(f(u)\ge f(x)\), so \(x\) is globally optimal. In computation, the same implication yields a certified stopping rule: with an exact oracle, stop when the gap is at most the requested objective tolerance. Unlike a step-size counter, this condition responds to the current geometry and gradient.

The exact-oracle argument can be packaged as a small Lean certificate. The first theorem shows the gap is nonnegative; the second shows it upper-bounds the primal error whenever the convex supporting inequality is available.

```lean
import Book.Models.FiniteOptimization

open Book.Models.FiniteOptimization

def linearMinimizer : Candidate := last
def frankWolfeGap (x : Candidate) : Nat := loss x - loss linearMinimizer

theorem frank_wolfe_gap_at_first : frankWolfeGap first = 4 := by decide

theorem frank_wolfe_gap_at_solution : frankWolfeGap linearMinimizer = 0 := by decide

structure LinearOracleCert {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (g s : E) : Prop where
  feasible : s ∈ X
  optimal : ∀ y, y ∈ X → inner ℝ g s ≤ inner ℝ g y

theorem frankWolfe_gap_nonnegative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {g x s : E} (hx : x ∈ X)
    (hcert : LinearOracleCert X g s) :
    0 ≤ inner ℝ g (x - s) := by
  have hopt := hcert.optimal x hx
  rw [inner_sub_right]
  linarith

theorem frankWolfe_gap_dominates_primal_error
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {f : E → ℝ} {g x xstar s : E}
    (hstar : xstar ∈ X) (hcert : LinearOracleCert X g s)
    (hsupport : f x - f xstar ≤ inner ℝ g (x - xstar)) :
    f x - f xstar ≤ inner ℝ g (x - s) := by
  calc
    f x - f xstar ≤ inner ℝ g (x - xstar) := hsupport
    _ ≤ inner ℝ g (x - s) := by
      have hopt := hcert.optimal xstar hstar
      rw [inner_sub_right, inner_sub_right]
      linarith
```

### 2.1 Approximate linear subproblems

An exact oracle may be unavailable. Suppose the returned point \(s_t\in X\) satisfies

\[
\langle\nabla f(x_t),s_t\rangle
\le \min_{s\in X}\langle\nabla f(x_t),s\rangle+\varepsilon_t,
\qquad \varepsilon_t\ge0.
\tag{98.6}
\]

Then its achieved linear decrease is within \(\varepsilon_t\) of the exact gap:

\[
\langle\nabla f(x_t),x_t-s_t\rangle
\ge g_{\mathrm{FW}}(x_t)-\varepsilon_t.
\tag{98.7}
\]

The achieved decrease in (98.7) is a lower bound on the exact gap, so by itself it is not an upper certificate for primal error. The accuracy guarantee supplies the missing direction: the exact gap is at most the achieved decrease plus \(\varepsilon_t\). A formalization should state whether the oracle returns an exact minimizer or an \(\varepsilon_t\)-optimal point; these produce different theorem hypotheses and an additional error term.

## 3. Curvature controls nonlinear progress

Convexity alone controls the linearization, but the objective can curve away from that linear model. Define the curvature constant

\[
C_f=
\sup_{\substack{x,s\in X\\0<\gamma\le1}}
\frac{2}{\gamma^2}\left(
f(x+\gamma(s-x))-f(x)
-\gamma\langle\nabla f(x),s-x\rangle
\right).
\tag{98.8}
\]

The point \(x+\gamma(s-x)\) is feasible because \(X\) is convex. The constant bounds the second-order remainder along feasible segments, not along arbitrary directions outside the domain. If \(\nabla f\) is \(L\)-Lipschitz on \(X\) in a norm \(\|\cdot\|\), then

\[
C_f\le L\,\operatorname{diam}_{\|\cdot\|}(X)^2.
\tag{98.9}
\]

This follows from the descent lemma: the remainder is at most \(\frac L2\|\gamma(s-x)\|^2\), and division by \(\gamma^2/2\) leaves \(L\|s-x\|^2\). The curvature constant is often sharper than a global smoothness constant times a squared diameter because it records only the objective's behavior along feasible chords.

Curvature is also affine invariant. If an affine change of variables parametrizes the same feasible set, both the feasible segments and their directional derivative remainders correspond, so \(C_f\) is unchanged. This is useful for comparing coordinate representations: a poor Euclidean diameter after reparameterization does not by itself mean the Frank–Wolfe analysis has worsened. The norm-based bound in (98.9) is a convenient estimate, not the definition of the method's geometry.

For the rate theorem, assume \(C_f<\infty\). Lipschitz continuity of the gradient on the compact feasible set is one sufficient condition; the theorem itself only needs the segment-remainder bound in (98.8).

For the update (98.2), the definition of \(C_f\) gives

\[
f(x_{t+1})
\le f(x_t)
+\gamma_t\langle\nabla f(x_t),s_t-x_t\rangle
+\frac{C_f}{2}\gamma_t^2.
\tag{98.10}
\]

With an exact LMO, the inner product is \(-g_{\mathrm{FW}}(x_t)\). Let \(h_t=f(x_t)-f(x^\star)\). By (98.5), \(g_{\mathrm{FW}}(x_t)\ge h_t\), so

\[
h_{t+1}
\le(1-\gamma_t)h_t+\frac{C_f}{2}\gamma_t^2.
\tag{98.11}
\]

For an \(\varepsilon_t\)-accurate LMO, the corresponding recurrence is

\[
h_{t+1}
\le(1-\gamma_t)h_t+\gamma_t\varepsilon_t
+\frac{C_f}{2}\gamma_t^2.
\tag{98.12}
\]

The accuracy term is multiplied by the step size because an approximate oracle affects the linear decrease for that round.

## 4. A finite-horizon \(O(1/T)\) guarantee

Use the schedule

\[
\gamma_t=\frac{2}{t+2},\qquad t=0,1,2,\ldots.
\tag{98.13}
\]

The first step has \(\gamma_0=1\). Since \(g_{\mathrm{FW}}(x_0)\ge h_0\), (98.10) yields \(h_1\le C_f/2\). We now show by induction that

\[
h_t\le\frac{2C_f}{t+2},\qquad t\ge1.
\tag{98.14}
\]

Assume the bound at time \(t\). Substitute (98.13) into (98.11):

\[
h_{t+1}
\le\frac{t}{t+2}\frac{2C_f}{t+2}
+\frac{2C_f}{(t+2)^2}
=\frac{2C_f(t+1)}{(t+2)^2}
\le\frac{2C_f}{t+3}.
\]

The final inequality is equivalent to \((t+1)(t+3)\le(t+2)^2\). This proves the induction. After \(T\ge1\) updates,

\[
f(x_T)-f(x^\star)\le\frac{2C_f}{T+2}.
\tag{98.15}
\]

The rate is sublinear, but each iteration solves only a linear problem and performs a convex combination. The theorem does not promise a small Frank–Wolfe gap at the final iterate from this primal recurrence alone. The gap remains a valid certificate whenever it is computed, and stronger primal-dual analyses can bound the gap of a selected iterate.

### 4.1 What the rate counts

To ensure objective error at most \(\epsilon\), (98.15) requires on the order of \(C_f/\epsilon\) LMO calls. This counts oracle calls, not their implementation cost: a simplex oracle is a coordinate scan, while a matrix oracle may require a leading singular-vector computation. If \(C_f\) is unknown, an exact duality gap can certify stopping without estimating it. A line search that minimizes \(f(x_t+\gamma(s_t-x_t))\) over \(0\le\gamma\le1\) performs at least as well as the prescribed \(\gamma_t\) in objective value, although the line-search computation may be expensive. The standard rate is therefore an oracle-complexity statement; practical efficiency still depends on the geometry of \(X\).

With approximate subproblems, (98.12) adds \(\gamma_t\varepsilon_t\). A constant oracle error creates a residual contribution that does not vanish under this schedule. To preserve an \(O(1/T)\) rate, choose accuracies that decrease appropriately or use an analysis that explicitly accounts for the total weighted error \(\sum_t\gamma_t\varepsilon_t\).

For example, suppose \(\varepsilon_t\le E/(t+2)\) for a constant \(E\ge0\). Then (98.12) and (98.13) add at most \(2(C_f+E)/(t+2)^2\) at round \(t\). The same induction gives

\[
h_T\le\frac{2(C_f+E)}{T+2},\qquad T\ge1.
\tag{98.18}
\]

The base case follows from \(h_1\le\varepsilon_0+C_f/2\le(C_f+E)/2\). This example shows how to carry an oracle's certified numerical tolerance into the final objective guarantee instead of treating it as an informal implementation detail.

## 5. Two linear oracles in action

### 5.1 The probability simplex adds one vertex

Let \(X=\{x\in\mathbb R^n:x_i\ge0,\ \sum_i x_i=1\}\). Given a gradient \(g\), minimizing \(\langle g,s\rangle\) over \(X\) selects a coordinate \(j\) with \(g_j=\min_i g_i\); an oracle solution is the vertex \(e_j\). The update becomes

\[
x_{t+1}=(1-\gamma_t)x_t+\gamma_t e_j.
\tag{98.16}
\]

If \(x_0\) is a vertex, each iteration adds at most one new vertex to its convex representation. After \(T\) updates, \(x_T\) has a representation supported on at most \(T+1\) vertices. The iterate may be stored as the mixture weights of these selected atoms rather than a dense vector. This sparsity is useful when \(n\) is huge and the desired solution is itself sparse.

### 5.2 The Euclidean ball uses a normalized gradient

For the ball \(X=\{s:\|s\|_2\le R\}\), if \(g\ne0\), the LMO solution is

\[
s=-R\frac{g}{\|g\|_2}.
\tag{98.17}
\]

If \(g=0\), every point in the ball minimizes the linear objective, and the algorithm can choose \(s=x_t\), which makes the update stationary. The oracle uses a norm and scaling rather than a projection. On other sets, a simplex vertex, a permutation, or a rank-one matrix may serve as the returned atom.

### 5.3 A nuclear-norm ball adds rank-one atoms

For matrices with the Frobenius inner product, the feasible set may be a nuclear-norm ball \(\{S:\|S\|_*\le\tau\}\). The dual norm of the nuclear norm is the operator norm. If \(u,v\) are top left and right singular vectors of the gradient matrix \(G\), then \(s=-\tau uv^\mathsf T\) minimizes \(\langle G,S\rangle\) over this ball. It is rank one. Starting at a rank-one atom, each Frank–Wolfe update forms a convex combination with one more rank-one atom, so the iterate has rank at most \(T+1\) after \(T\) rounds. This is an example where the oracle produces a structured low-rank direction while a projection may require a full singular-value thresholding operation.

The two examples share a formal interface despite different implementations: prove feasibility of the returned \(s\), prove its linear optimality, and pass those facts to the generic iteration theorem.

## 6. Lean proof architecture

### 6.1 Package the linear-oracle certificate

In a real inner-product space, define the certificate independently of the optimization algorithm:

~~~lean
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure LinearOracleCert (X : Set E) (g s : E) : Prop where
  feasible : s ∈ X
  optimal : ∀ y, y ∈ X → inner ℝ g s ≤ inner ℝ g y
~~~

The simplex and ball examples prove this certificate with different local arguments. The generic Frank–Wolfe step consumes only the certificate and the step-size bounds. It does not need to know how the oracle solved its subproblem.

### 6.2 Keep feasibility as an affine-combination lemma

Prove once that if \(x,s\in X\), \(X\) is convex, and \(0\le\gamma\le1\), then \((1-\gamma)x+\gamma s\in X\). This is the sole feasibility fact needed by the iteration. Avoid re-proving coordinate nonnegativity or norm bounds inside every algorithm-specific theorem.

### 6.3 Separate curvature from recurrence algebra

Package (98.8) as a segment inequality that can be applied to \(x_t,s_t,\gamma_t\). A one-step lemma then combines that inequality with the LMO certificate and convexity to establish (98.11). The finite-horizon rate is a separate induction over \(t\), using only the scalar recurrence and the arithmetic identity for the chosen step schedule.

For approximate oracles, add an explicit error field to the certificate and preserve \(\varepsilon_t\) through the recurrence. Do not coerce an approximate optimality condition into exact equality; the error's coefficient \(\gamma_t\) matters in the final sum.

### 6.4 Preserve atomic representations when needed

For \(X=\operatorname{conv}(A)\), record the iterate as a finite convex combination of atoms. The update scales old weights by \(1-\gamma_t\) and adds the new atom with weight \(\gamma_t\). A dependent representation can carry both the weights summing to one and the equality to the ambient vector. This makes the sparsity theorem a finite-support argument rather than a post-hoc statement about coordinates.

~~~text
gradient at x_t
      |
      v
linear oracle certificate ----> feasible atom s_t
      |                                  |
      +---------- curvature bound -------+
                         |
                         v
               one-step gap recurrence
                         |
                         v
              finite induction on t
                         |
                         v
                 objective-gap rate
~~~

## 7. Common failure modes

1. **Assuming the LMO is a projection.** It minimizes a linear functional and may return a distant vertex.
2. **Forgetting the step-size interval.** Feasibility of the convex-combination update uses \(0\le\gamma_t\le1\).
3. **Using curvature outside the feasible segment.** The constant in (98.8) controls only \(x+\gamma(s-x)\) for feasible endpoints.
4. **Confusing the primal error and the Frank–Wolfe gap.** The gap upper-bounds error, but the primal recurrence alone does not bound the final gap.
5. **Dropping the \(\gamma_t\varepsilon_t\) term.** Inexact linear solves reduce the certified descent.
6. **Claiming every iterate is sparse without an atomic representation.** The support statement applies to a chosen convex decomposition and its updates.
7. **Ignoring the cost of the linear oracle.** Projection-free is useful only when the linear subproblem is cheaper or more structured.
8. **Assuming linear convergence from strong convexity alone.** Standard Frank–Wolfe has a general \(O(1/T)\) rate; linear rates require additional geometry or algorithm variants.
9. **Using an unconstrained smoothness bound where curvature is needed.** The segment remainder should match the feasible domain.
10. **Proving the simplex, ball, and generic theorems together.** Prove each oracle certificate separately, then reuse the generic analysis.

## 8. Exercises

1. Prove that the Frank–Wolfe gap (98.3) upper-bounds \(f(x)-f(x^\star)\).
2. Derive the curvature inequality (98.10) from definition (98.8).
3. Prove the one-step recurrence (98.11), including the role of the exact LMO.
4. Verify the base case and induction step for the rate (98.14).
5. Derive the approximate-oracle recurrence (98.12).
6. Prove that a simplex LMO returns a vertex at a minimum-gradient coordinate.
7. Prove the Euclidean-ball oracle formula (98.17), including the zero-gradient case.
8. Show that the simplex iterate has a representation with at most \(T+1\) atoms after \(T\) updates from a vertex.
9. Bound \(C_f\) by \(L\operatorname{diam}(X)^2\) under an \(L\)-Lipschitz gradient.
10. Formalize the linear-oracle certificate and prove the generic feasibility update.
11. State a Lean theorem for the scalar recurrence before connecting it to the optimization iterate.
12. Explain why an away-step or fully corrective variant needs additional state beyond a single convex-combination update.

## 9. Chapter summary

Frank–Wolfe replaces Euclidean projection with a linear optimization oracle. The linear oracle supplies a computable gap that upper-bounds objective suboptimality. A curvature constant controls the nonlinear remainder along feasible segments, yielding a scalar recurrence and an \(O(1/T)\) primal error bound for the standard step schedule.

Convex-combination updates preserve feasibility and can preserve sparse atomic representations. In Lean, separate the exact or approximate oracle certificate, segment-curvature bound, affine feasibility lemma, and finite recurrence. Algorithm-specific geometry belongs in the oracle implementation, while the convergence theorem remains reusable.

## Further reading

- Jaggi, [“Revisiting Frank–Wolfe: Projection-Free Sparse Convex Optimization”](https://proceedings.mlr.press/v28/jaggi13.html), for curvature-based primal and duality-gap results, sparse convex-hull methods, and inexact linear oracles.
- Lacoste-Julien and Jaggi, [“On the Global Linear Convergence of Frank–Wolfe Optimization Variants”](https://arxiv.org/abs/1511.05932), for away-step, pairwise, and fully corrective variants with stronger geometric assumptions.
- Chapter 92 — Projected Gradient and Proximal Methods, for the projection-based constrained methods that Frank–Wolfe avoids.
