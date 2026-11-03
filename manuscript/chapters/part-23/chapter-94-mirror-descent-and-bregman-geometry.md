# Chapter 94 — Mirror Descent and Bregman Geometry

> **Audience.** This chapter assumes familiarity with subgradients, projections, and convex optimization from Chapters 90–92. It replaces Euclidean distance with a geometry adapted to the feasible set and derives mirror descent's online regret bound from a three-point identity.

Euclidean gradient methods measure every step with the same squared norm. That geometry is natural for unconstrained problems and boxes, but can be inefficient on a simplex or a highly nonuniform domain. Mirror descent changes the distance model without changing the central proof pattern: choose a strongly convex reference function, form its Bregman divergence, and telescope a one-step inequality.

The method also connects static optimization to online learning. At each round, a convex loss is revealed through a subgradient. The learner updates before seeing the next loss, and the theorem bounds cumulative loss against any fixed comparator. The proof is a precise example of how a potential function turns local optimality into a global finite-horizon guarantee.

## Learning objectives

After this chapter, you should be able to:

- define Bregman divergence and distinguish its argument order;
- derive mirror descent's variational inequality and three-point relation;
- prove the standard regret bound using strong convexity and a dual norm;
- recover projected subgradient descent from a quadratic mirror map;
- derive exponentiated-gradient updates from negative entropy on the simplex;
- design Lean interfaces that separate the algebraic identity, optimizer certificate, and finite-sum argument.

## 1. Bregman divergence encodes a choice of geometry

Let \(E\) be a finite-dimensional real inner-product space, and let \(\psi\) be differentiable and convex on a convex domain containing the points under consideration. Its Bregman divergence is

\[
D_\psi(x,y)=\psi(x)-\psi(y)-\langle\nabla\psi(y),x-y\rangle.
\tag{94.1}
\]

The second argument is the point at which the tangent plane is taken. Convexity implies \(D_\psi(x,y)\ge0\), but generally

\[
D_\psi(x,y)\ne D_\psi(y,x).
\tag{94.2}
\]

It need not satisfy a triangle inequality either. “Divergence” is safer language than “distance.” Its usefulness comes from the exact algebra of tangent remainders, not from symmetry.

For the quadratic reference \(\psi(x)=\tfrac12\|x\|_2^2\),

\[
D_\psi(x,y)=\frac12\|x-y\|_2^2.
\tag{94.3}
\]

The ordinary squared distance is therefore one Bregman divergence. A different \(\psi\) produces a different geometry. The design decision is to choose a reference function whose divergence is small in relevant feasible directions and whose strong convexity can control step errors.

### 1.1 The three-point identity

For any \(u,x,p\) in the domain, expand the three divergences using (94.1):

\[
D_\psi(u,x)-D_\psi(u,p)-D_\psi(p,x)
=\langle\nabla\psi(p)-\nabla\psi(x),u-p\rangle.
\tag{94.4}
\]

This identity is the Bregman counterpart of the squared-norm polarization formula. It keeps the argument order visible. In the Euclidean case, substituting (94.3) recovers

\[
\frac12\|u-x\|^2-\frac12\|u-p\|^2-\frac12\|p-x\|^2
=\langle p-x,u-p\rangle.
\]

The right side is exactly the cross term that appears when the first-order condition of a proximal minimization is paired with a comparator. This is why the identity is central to mirror-descent proofs.

The Lean example below defines the divergence with the same argument order and proves the identity without any convexity or differentiability hypotheses. Those assumptions are needed for nonnegativity and algorithmic use, but not for this algebraic cancellation.

```lean
import Book.Models.FiniteOptimization

open Book.Models.FiniteOptimization

def bregmanSquare (x y : Int) : Int := (x - y) * (x - y)

theorem bregman_example_value : bregmanSquare 3 1 = 4 := by decide

theorem bregman_equal_points_vanish (x : Int) : bregmanSquare x x = 0 := by simp [bregmanSquare]

def BregmanDiv {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (psi : E → ℝ) (gradPsi : E → E) (x y : E) : ℝ :=
  psi x - psi y - inner ℝ (gradPsi y) (x - y)

theorem bregman_three_point_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (psi : E → ℝ) (gradPsi : E → E) (u x p : E) :
    BregmanDiv psi gradPsi u x - BregmanDiv psi gradPsi u p -
        BregmanDiv psi gradPsi p x =
      inner ℝ (gradPsi p - gradPsi x) (u - p) := by
  unfold BregmanDiv
  have hux : u - x = (u - p) + (p - x) := by abel
  rw [hux, inner_add_right, inner_sub_left]
  ring
```

### 1.2 Strong convexity supplies a norm bound

Suppose \(\psi\) is \(\sigma\)-strongly convex with respect to a norm \(\|\cdot\|\), meaning

\[
D_\psi(x,y)\ge\frac{\sigma}{2}\|x-y\|^2.
\tag{94.5}
\]

Let \(\|\cdot\|_*\) denote the dual norm. Hölder's inequality gives
\[
\langle g,d\rangle\le\|g\|_*\|d\|.
\]
The norm and dual norm must match the strong-convexity statement. Using a Euclidean bound for a regularizer that is strongly convex only in the one-norm, for example, breaks the rate proof.

## 2. The mirror update and its optimality certificate

Let \(C\) be a nonempty convex feasible set and let \(x_t\in C\). Given a subgradient \(g_t\) of the round-\(t\) loss at \(x_t\), define the next point as a minimizer of

\[
x_{t+1}\in\mathop{\rm argmin}_{x\in C}
\left\{\eta\langle g_t,x\rangle+D_\psi(x,x_t)\right\},
\tag{94.6}
\]

where \(\eta>0\) is the learning rate. The first term linearizes the current loss; the divergence penalizes changing the decision. The minimum may require a closedness and coercivity argument, so existence should be stated separately from the optimality condition.

For any comparator \(u\in C\), first-order optimality of \(x_{t+1}\) gives

\[
\left\langle
\eta g_t+\nabla\psi(x_{t+1})-\nabla\psi(x_t),
u-x_{t+1}
\right\rangle\ge0.
\tag{94.7}
\]

Use (94.4) to rewrite the gradient difference. Rearranging yields the three-point inequality

\[
\eta\langle g_t,x_{t+1}-u\rangle
\le D_\psi(u,x_t)-D_\psi(u,x_{t+1})-D_\psi(x_{t+1},x_t).
\tag{94.8}
\]

The negative final divergence records the price of moving. It is not optional bookkeeping: strong convexity will use it to absorb the part of the regret involving the distance between \(x_t\) and \(x_{t+1}\).

## 3. A finite-horizon regret bound

Consider a sequence of convex losses \(f_1,\ldots,f_T\). At round \(t\), the method predicts \(x_t\), observes a subgradient \(g_t\in\partial f_t(x_t)\), and then computes \(x_{t+1}\) using (94.6). By convexity,

\[
f_t(x_t)-f_t(u)\le\langle g_t,x_t-u\rangle.
\tag{94.9}
\]

Split the displacement at the new point:

\[
\langle g_t,x_t-u\rangle
=\langle g_t,x_t-x_{t+1}\rangle
+\langle g_t,x_{t+1}-u\rangle.
\]

Apply (94.8) to the second term. For the first, use strong convexity (94.5) and Young's inequality:

\[
\eta\langle g_t,x_t-x_{t+1}\rangle
-D_\psi(x_{t+1},x_t)
\le
\eta\|g_t\|_*\|x_t-x_{t+1}\|
-\frac{\sigma}{2}\|x_t-x_{t+1}\|^2
\le\frac{\eta^2}{2\sigma}\|g_t\|_*^2.
\tag{94.10}
\]

Combining (94.8)–(94.10) gives a one-round inequality:

\[
\eta(f_t(x_t)-f_t(u))
\le D_\psi(u,x_t)-D_\psi(u,x_{t+1})
+\frac{\eta^2}{2\sigma}\|g_t\|_*^2.
\tag{94.11}
\]

Sum over \(t=1,\ldots,T\). The divergence terms telescope, leaving

\[
\sum_{t=1}^T(f_t(x_t)-f_t(u))
\le \frac{D_\psi(u,x_1)}{\eta}
+\frac{\eta}{2\sigma}\sum_{t=1}^T\|g_t\|_*^2.
\tag{94.12}
\]

If \(D_\psi(u,x_1)\le D\) for every feasible comparator and \(\|g_t\|_*\le G\), then

\[
\operatorname{Regret}_T(u)
\le\frac{D}{\eta}+\frac{\eta G^2T}{2\sigma}.
\tag{94.13}
\]

For \(D>0\), \(G>0\), and \(T\ge1\), choosing \(\eta=\sqrt{2\sigma D/(G^2T)}\) balances the two terms and gives

\[
\operatorname{Regret}_T(u)\le G\sqrt{\frac{2DT}{\sigma}}.
\tag{94.14}
\]

The average regret is therefore \(O(T^{-1/2})\). If the same convex loss is used every round, an averaged iterate can be converted into a bound on static optimization error. For arbitrary changing losses, regret compares the learner to one fixed decision; it does not assert that the iterates converge to a minimizer of any single objective.

The proof has four interfaces. The subgradient inequality linearizes the loss; the mirror-step certificate and three-point identity produce the potential difference; strong convexity absorbs the movement within a round; summation telescopes the potential.

~~~text
subgradient at x_t  --->  split loss at x_{t+1}
                                  |
mirror optimality  --->  three-point identity
                                  |
strong convexity + Young's inequality
                                  v
                      one-round regret bound
                                  |
                            sum over t
                                  v
                    telescoping potential bound
~~~

### 3.1 Why the learning rate has this form

The first term in (94.13) is the initial geometric distance divided by the step size. A small step moves cautiously and pays more for the initial mismatch. The second term accumulates the cost of subgradients and grows with the step size. Balancing these terms gives the square-root horizon dependence. If \(T\) is not known ahead of time, decreasing learning rates or doubling schedules can be used, but each schedule needs its own finite-sum proof.

The generic theorem is deliberately stated against an arbitrary comparator \(u\). In an application, select \(u\) after the loss sequence is known, for example the best fixed decision in hindsight. The proof remains valid because (94.11) holds for every feasible \(u\) at every round.

## 4. Two geometries as worked examples

### 4.1 Euclidean projection is mirror descent

Choose \(\psi(x)=\tfrac12\|x\|_2^2\). Then \(D_\psi(x,x_t)=\tfrac12\|x-x_t\|_2^2\), and the update (94.6) becomes

\[
x_{t+1}\in\mathop{\rm argmin}_{x\in C}
\left\{\eta\langle g_t,x\rangle+\frac12\|x-x_t\|_2^2\right\}.
\]

Complete the square:

\[
\eta\langle g_t,x\rangle+\frac12\|x-x_t\|^2
=\frac12\|x-(x_t-\eta g_t)\|^2+\text{constant}.
\]

Thus \(x_{t+1}=P_C(x_t-\eta g_t)\). The projected subgradient method is exactly mirror descent with a quadratic reference function. Chapter 92's projection theorem and variational inequality are the Euclidean instance of the general proximal optimality condition.

### 4.2 Negative entropy yields exponentiated gradient

Let \(C\) be the probability simplex and take

\[
\psi(x)=\sum_{i=1}^n x_i\log x_i.
\]

For points with positive coordinates, its Bregman divergence is the Kullback–Leibler divergence

\[
D_\psi(x,y)=\sum_{i=1}^n x_i\log\frac{x_i}{y_i}.
\tag{94.15}
\]

The mirror update with a linear loss \(g_t\) solves
\[
\min_{x\in C}\left\{\eta\langle g_t,x\rangle
+\sum_i x_i\log\frac{x_i}{x_{t,i}}\right\}.
\]
Introduce a multiplier for the constraint \(\sum_i x_i=1\). The stationarity equation gives \(x_{t+1,i}\) proportional to \(x_{t,i}e^{-\eta g_{t,i}}\); normalization yields

\[
x_{t+1,i}
=\frac{x_{t,i}e^{-\eta g_{t,i}}}
{\sum_j x_{t,j}e^{-\eta g_{t,j}}}.
\tag{94.16}
\]

Starting from the uniform distribution, the divergence to a vertex of the simplex is \(\log n\). Negative entropy is 1-strongly convex on the simplex with respect to the one-norm, and the dual norm is the infinity norm. If \(\|g_t\|_\infty\le1\), (94.14) gives

\[
\operatorname{Regret}_T\le\sqrt{2T\log n}.
\tag{94.17}
\]

The dependence is logarithmic in the number of choices. Euclidean projected descent on the simplex instead pairs the two-norm with itself; when each coordinate of a gradient is bounded by one, its two-norm can be as large as \(\sqrt n\), giving a \(\sqrt n\) dimension factor in the generic bound. Entropy matches the geometry of probability vectors and uses the infinity norm for coordinatewise gradient bounds.

The entropy gradient is defined on the relative interior of the simplex. The function \(x\log x\) extends continuously to zero by the convention \(0\log 0=0\), so a comparator may lie on the boundary even though the update remains in the positive simplex. A formal development can keep iterates positive, use extended-real boundary values, or prove a regularized variant. The domain is part of the theorem, not a harmless implementation detail.

### 4.3 Choosing a mirror map

The mirror map is selected by comparing two quantities: how far a comparator can be from the initial point in Bregman divergence, and how large the observed subgradients are in the dual norm. These are the quantities \(D\) and \(G\) in (94.14). A map that makes one small can make the other large, so the relevant comparison is \(G\sqrt{D/\sigma}\), not the diameter alone.

For a simplex with many coordinates, entropy has a logarithmic initial divergence to a vertex and pairs the one-norm with the infinity norm. For a region described by ordinary Euclidean constraints, the quadratic map often gives simpler projection and derivative lemmas. On a positive cone or a domain where approaching the boundary is costly, a logarithmic barrier may be appropriate, although its gradient becomes unbounded near that boundary and the analysis must control local norms. There is no universally best mirror map: it encodes which directions in the problem should count as expensive.

Before formalizing a new choice, calculate its divergence, prove its strong-convexity modulus in the intended norm, and bound the dual norm of the loss subgradients. Then check that the update remains in the domain where the gradient and divergence are defined. This small analytic audit predicts the eventual rate and often exposes a poor geometry before any long Lean proof begins.

### 4.4 From regret to a static optimization bound

Suppose every round uses the same convex function \(f\), and let \(x_1,\ldots,x_T\) be the predictions made before each update. Define their average by

\[
\bar x_T=\frac1T\sum_{t=1}^T x_t.
\]

Convexity of \(C\) makes \(\bar x_T\) feasible, while Jensen's inequality gives

\[
f(\bar x_T)-f(u)
\le\frac1T\sum_{t=1}^T(f(x_t)-f(u)).
\]

If \(u\) minimizes \(f\) on \(C\), the regret theorem bounds the right side by \(G\sqrt{2D/(\sigma T)}\). Thus the average prediction has an objective gap of order \(T^{-1/2}\). This is an online-to-batch conversion: the online theorem is proved first, and convexity then converts its cumulative comparison into a static guarantee. For a stronger rate, additional assumptions such as smoothness or strong convexity are needed; averaging alone does not improve the generic worst-case exponent.

This guarantee is for the average, not necessarily for the last update \(x_{T+1}\). In a formal proof, record which sequence is being averaged: the predictions \(x_t\) made at each round, the post-update points, or a weighted sequence. These conventions differ by an index shift, and the one-step theorem must match the chosen sequence exactly.

## 5. Lean proof architecture

### 5.1 Define the divergence with its argument order

A local definition can make the orientation explicit:

~~~lean
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def BregmanDiv (psi : E → ℝ) (gradPsi : E → E) (x y : E) : ℝ :=
  psi x - psi y - inner ℝ (gradPsi y) (x - y)
~~~

Passing the gradient as a separate function keeps the algebraic definition independent from differentiability. A later structure can package that the function is the actual derivative of \(\psi\), the domain is convex, and \(\psi\) is strongly convex with respect to a chosen norm.

Prove the three-point identity as a standalone lemma. It is mostly cancellation and bilinearity of the inner product; the analytical convexity hypotheses are not needed for the identity itself. Nonnegativity of the divergence is a separate theorem that does use convexity. Keeping these claims separate makes it harder to accidentally use nonnegativity as if it were symmetry.

### 5.2 Package the mirror-step certificate

For a proposed update \(p\), the key data are:

- feasibility \(p\in C\);
- the first-order inequality (94.7) for every \(u\in C\);
- the strong-convexity lower bound for \(D_\psi(p,x_t)\).

The mirror-step theorem can accept these facts without unfolding an argmin. Existence and uniqueness of the minimizer are proved separately from closedness, convexity, and coercivity assumptions. This resembles the projection-certificate design from Chapter 92, but the divergence is now asymmetric and generally nonlinear.

### 5.3 Match the primal and dual norms

Represent the primal norm and its dual norm explicitly in theorem statements. The regret proof uses
\(\langle g,d\rangle\le\|g\|_*\|d\|\), then absorbs \(\|d\|\) with the strong-convexity modulus \(\sigma\). A mismatch between the norm in (94.5) and the dual norm used for gradients invalidates (94.10).

For simplex entropy, the natural pair is the one-norm and infinity norm. For the quadratic map, both are the Euclidean norm. Avoid hiding this choice behind a generic norm unless the duality pairing and strong-convexity interface are also explicit.

### 5.4 Telescope over a finite horizon

Define the online history as a finite sequence or a function on \(\mathrm{Fin}(T)\). Prove (94.11) for one round, sum it using a finite-sum theorem, and normalize by the positive learning rate. Keep the comparator fixed throughout the sum. If the comparator varies with \(t\), the divergence terms no longer telescope without an additional movement penalty.

For exponentiated gradient, prove the coordinate update separately from the generic regret theorem. The derivation needs positivity, logarithm identities, and a normalization constant. Then apply the generic bound using the KL divergence and the one/infinity dual-norm pair. This keeps special-function algebra out of the general mirror-descent proof.

### 5.5 Formalize the online-to-batch step separately

Once the regret theorem is available, the conversion to a static optimization estimate should not reopen the mirror-update proof. State a finite Jensen inequality for the average of feasible points, combine it with the regret sum, and divide by the positive horizon. In Lean, make positivity of \(T\) explicit before using \(1/T\), and keep the minimizer hypothesis separate from convexity. A nonempty feasible set and existence of a minimizer are needed only when selecting \(u\); the regret theorem itself works for any chosen comparator.

This separation is useful beyond mirror descent. Any algorithm that proves the same cumulative comparison can reuse the online-to-batch lemma, even if its update rule and potential are different. It also clarifies the exact logical dependencies: convexity supplies Jensen, while the algorithm supplies regret.

## 6. Common failure modes

1. **Reversing the divergence arguments.** \(D_\psi(u,x_t)\) is the comparator-to-current potential in (94.11).
2. **Treating a Bregman divergence as a metric.** It may be asymmetric and need not satisfy a triangle inequality.
3. **Using the wrong dual norm.** Pair the subgradient norm with the primal norm controlled by strong convexity.
4. **Dropping the step divergence.** \(D_\psi(x_{t+1},x_t)\) absorbs the within-round movement term.
5. **Assuming the mirror update exists automatically.** State domain, closedness, and coercivity conditions.
6. **Forgetting that the comparator is fixed.** A changing comparator adds terms to the telescope.
7. **Claiming last-iterate convergence from a regret bound.** Regret controls cumulative comparison, not necessarily convergence of \(x_t\).
8. **Using entropy at the simplex boundary without a domain argument.** Logarithms require positive coordinates or an extended-real formulation.
9. **Confusing logarithmic dimension dependence with dimension-free bounds.** The entropy example has a \(\log n\) term.
10. **Proving the update and regret theorem together.** First isolate the three-point inequality, then prove the finite-horizon bound.

## 7. Exercises

1. Prove the three-point identity (94.4) by expanding all three divergences.
2. Derive (94.8) from the variational inequality (94.7).
3. Starting from (94.9), prove the one-round bound (94.11).
4. Sum (94.11) and optimize the learning rate to obtain (94.14).
5. Show that the quadratic mirror map makes the mirror update equal to Euclidean projection.
6. Derive the exponentiated-gradient update (94.16) using a Lagrange multiplier.
7. Prove that \(D_\psi(x,y)\ge0\) for a differentiable convex \(\psi\), and give a strictly convex \(\psi\) for which the divergence is asymmetric.
8. Identify the primal norm and dual norm for negative entropy on the simplex and verify the regret bound under \(\|g_t\|_\infty\le1\).
9. Formalize BregmanDiv and its three-point identity for a real inner-product space.
10. Design a structure containing the mirror-step certificate and prove (94.11) without defining an argmin function.
11. Give an example where low regret does not imply that the sequence of decisions converges.

## 8. Chapter summary

Mirror descent replaces squared Euclidean distance with a Bregman divergence generated by a convex reference function. The optimizer's first-order condition and the three-point identity give a one-round inequality. Strong convexity of the reference function absorbs the movement term, and summing the inequalities telescopes the comparator divergence into an \(O(\sqrt T)\) regret guarantee.

Quadratic geometry recovers projected subgradient descent. Negative entropy on the simplex gives exponentiated gradient and logarithmic dependence on the number of choices. In Lean, keep argument order, primal/dual norms, optimizer certificates, and finite-horizon summation explicit. Those interfaces make one proof apply across multiple geometries.

## Further reading

- Beck and Teboulle, [“Mirror Descent and Nonlinear Projected Subgradient Methods for Convex Optimization”](https://www.sciencedirect.com/science/article/pii/S0167637702002316), for the Bregman-projection view and entropy mirror descent.
- Beck, [*First-Order Methods in Optimization*, Chapter 9](https://epubs.siam.org/doi/10.1137/1.9781611974997.ch9), for mirror descent and non-Euclidean projected subgradient methods.
- Nemirovski and Yudin, *Problem Complexity and Method Efficiency in Optimization*, for the classical complexity viewpoint on mirror methods.
