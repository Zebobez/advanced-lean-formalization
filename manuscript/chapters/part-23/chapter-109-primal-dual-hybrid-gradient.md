# Chapter 109 — Primal–Dual Hybrid Gradient and Proximal Splitting

> **Audience.** This chapter builds on proximal maps from Chapter 92 and the saddle-point certificates from Chapter 108. It develops the primal–dual hybrid gradient method for composite convex objectives, emphasizing the operator-norm condition and the averaged gap theorem.

Fenchel duality rewrites a composite objective as a convex–concave saddle problem. The primal–dual hybrid gradient method (PDHG), also called the Chambolle–Pock method in its standard form, uses a proximal step for the dual variable, a proximal step for the primal variable, and an extrapolated primal point in the next dual update.

The proof has a useful structure for formalization. Proximal optimality gives two three-point inequalities. The bilinear coupling creates a cross term involving the operator and its adjoint. A step-size condition makes the associated block quadratic form positive, allowing the inequalities to telescope. The convergence statement then applies to an ergodic average and a restricted primal–dual gap.

## Learning objectives

After this chapter, you should be able to:

- derive the saddle formulation for minimizing \(G(x)+F(Kx)\);
- write the PDHG iteration and identify the role of extrapolation;
- derive the KKT conditions from proximal optimality;
- explain the condition \(\tau\sigma\|K\|^2<1\) through a positive block operator;
- state the restricted ergodic gap bound and distinguish it from a last-iterate guarantee;
- formalize the proof using proximal inequalities, adjoints, and a finite telescope.

## 1. Composite objectives and saddle structure

### 1.1 The primal and dual problems

Let \(X,Y\) be real Hilbert spaces, \(K:X\to Y\) a bounded linear map, and \(G:X\to(-\infty,+\infty]\), \(F:Y\to(-\infty,+\infty]\) proper, lower semicontinuous, and convex. Consider
\[
\min_{x\in X} G(x)+F(Kx).
\tag{109.1}
\]
By Fenchel conjugacy,
\[
F(Kx)=\sup_{y\in Y}\{\langle Kx,y\rangle-F^*(y)\}.
\tag{109.2}
\]
The resulting saddle function is
\[
L(x,y)=G(x)+\langle Kx,y\rangle-F^*(y).
\tag{109.3}
\]
The primal problem is \(\min_x\sup_y L(x,y)\), and the associated dual objective is
\[
\max_y -G^*(-K^*y)-F^*(y).
\tag{109.4}
\]
The adjoint \(K^*\) is forced by the identity
\(\langle Kx,y\rangle=\langle x,K^*y\rangle\). This sign and placement should be derived from the pairing rather than memorized from one application.

A saddle point \((x^\star,y^\star)\) satisfies
\[
Kx^\star\in\partial F^*(y^\star),\qquad
-K^*y^\star\in\partial G(x^\star).
\tag{109.5}
\]
These are the KKT conditions. They connect the two proximal steps directly to optimality: at a solution, each prox update leaves its variable fixed when the other variable is held at its solution value.

### 1.2 Proximal maps as implicit subgradient steps

For \(\tau>0\), define
\[
\operatorname{prox}_{\tau G}(z)
=\arg\min_u\left\{G(u)+\frac1{2\tau}\|u-z\|^2\right\}.
\tag{109.6}
\]
Strong convexity of the quadratic term gives a unique minimizer when \(G\) is proper, lower semicontinuous, and convex. Its optimality condition is
\[
p=\operatorname{prox}_{\tau G}(z)
\quad\Longleftrightarrow\quad
\frac{z-p}{\tau}\in\partial G(p).
\tag{109.7}
\]
The prox is therefore an implicit subgradient step. It handles the nonsmooth part exactly rather than approximating it by an ordinary gradient.

A second consequence, used in convergence proofs, is the three-point inequality:
\[
G(p)+\frac1{2\tau}\|p-z\|^2
+\frac1{2\tau}\|u-p\|^2
\le G(u)+\frac1{2\tau}\|u-z\|^2.
\tag{109.8}
\]
It follows by applying the subgradient inequality at \(p\) with subgradient \((z-p)/\tau\), then expanding the squared norms. The same result applies to \(F^*\) with step \(\sigma\).


## 2. The primal–dual hybrid gradient iteration

### 2.1 Dual step, primal step, extrapolation

Choose steps \(\tau,\sigma>0\), initialize \(x^0,y^0\), and set \(\bar x^0=x^0\). For \(k\ge0\), perform
\[
\begin{aligned}
y^{k+1}
&=\operatorname{prox}_{\sigma F^*}
  (y^k+\sigma K\bar x^k),\\
x^{k+1}
&=\operatorname{prox}_{\tau G}
  (x^k-\tau K^*y^{k+1}),\\
\bar x^{k+1}
&=x^{k+1}+\theta(x^{k+1}-x^k).
\end{aligned}
\tag{109.9}
\]
The standard Chambolle–Pock choice is \(\theta=1\). The dual update uses the extrapolated primal point \(\bar x^k\); the primal update uses the newly computed dual point \(y^{k+1}\). Reversing the order or using \(x^k\) instead of \(\bar x^k\) changes the method and its proof.

The iteration can be read as three steps:

1. a dual ascent step regularized by \(F^*\);
2. a primal descent step regularized by \(G\);
3. an extrapolation that feeds recent primal motion into the next dual update.

The extrapolation is not a feasibility operation and need not lie in a constraint set. Constraints are instead encoded in \(G\) or \(F^*\) through indicator functions, whose proximal maps are projections.

### 2.2 Recover the KKT conditions at a fixed point

Apply (109.7) to the dual update:
\[
\frac{y^k+\sigma K\bar x^k-y^{k+1}}{\sigma}
\in\partial F^*(y^{k+1}).
\tag{109.10}
\]
The primal update similarly gives
\[
\frac{x^k-\tau K^*y^{k+1}-x^{k+1}}{\tau}
\in\partial G(x^{k+1}).
\tag{109.11}
\]
At a fixed point with \(x^{k+1}=x^k=\bar x^k\) and \(y^{k+1}=y^k\), these reduce to
\[
Kx\in\partial F^*(y),\qquad -K^*y\in\partial G(x),
\]
which is exactly (109.5). The algorithm’s residuals are thus approximate versions of the saddle optimality conditions.

A fixed point calculation is not itself a convergence proof. It verifies that the update has the right solutions. Convergence depends on how the primal and dual errors interact across iterations.


## 3. Why the step sizes are coupled

### 3.1 The block quadratic form

The bilinear term produces products of primal and dual increments. These are controlled jointly, not by choosing \(\tau\) and \(\sigma\) independently. Consider the symmetric block operator
\[
M=
\begin{pmatrix}
\tau^{-1}I & -K^*\\
-K & \sigma^{-1}I
\end{pmatrix}.
\tag{109.12}
\]
For increments \(u\in X\), \(v\in Y\),
\[
\begin{aligned}
\left\langle
\begin{pmatrix}u\\v\end{pmatrix},
M\begin{pmatrix}u\\v\end{pmatrix}
\right\rangle
&=\frac{\|u\|^2}{\tau}+\frac{\|v\|^2}{\sigma}
-2\langle Ku,v\rangle\\
&\ge \frac{\|u\|^2}{\tau}+\frac{\|v\|^2}{\sigma}
-2\|K\|\|u\|\|v\|.
\end{aligned}
\tag{109.13}
\]
The scalar quadratic on the right is positive definite when
\[
\tau\sigma\|K\|^2<1.
\tag{109.14}
\]
This is the basic step-size condition. It ensures the primal and dual proximal regularization dominates the cross coupling.

The condition is sufficient for the standard convergence theorem; it is not a claim that every larger pair of steps must diverge for every particular problem. A tighter estimate, diagonal preconditioning, known structure, or line search may permit more flexible parameters. This chapter formalizes the global norm-based condition because it yields a clean reusable theorem.

The strict inequality also gives a useful margin. If \(q=\sqrt{\tau\sigma}\,\|K\|<1\), then Young's inequality bounds the cross term by
\[
2\|K\|\|u\|\|v\|
\le q\left(\frac{\|u\|^2}{\tau}+\frac{\|v\|^2}{\sigma}\right).
\tag{109.15}
\]
The block quadratic form is therefore at least \(1-q\) times the diagonal energy. This quantitative lower bound is more useful than bare nonnegativity: it lets a proof retain control of both increment norms. A Lean development can first prove the scalar inequality over nonnegative reals, then instantiate it with norms and the operator bound. That keeps square roots and real-number order reasoning out of the later saddle argument.

For finite-dimensional vectors, the same condition has a geometric interpretation. The diagonal blocks provide curvature in the primal and dual directions; the off-diagonal blocks \(K\) and \(K^*\) tilt those directions together. When the norm-scaled tilt is below one, the full block form remains positive. This picture explains why a large operator norm requires smaller steps in at least one of the two spaces.

### 3.2 The descent estimate and telescoping

Apply the three-point inequality (109.8) first to \(y^{k+1}\) and then to \(x^{k+1}\). The subgradient terms produce the saddle differences
\(L(x^{k+1},y)-L(x,y^{k+1})\). The bilinear term leaves a cross product of increments. Grouping those terms into the block quadratic form from (109.12) yields a one-step estimate of the form
\[
L(x^{k+1},y)-L(x,y^{k+1})
\le \mathcal E_k(x,y)-\mathcal E_{k+1}(x,y),
\tag{109.16}
\]
where \(\mathcal E_k\) is a nonnegative weighted squared-distance potential, with a coupling term when the extrapolation is included. Under (109.14), the coupling is controlled by the positive block form.

Summing (109.16) from \(k=0\) to \(N-1\) cancels the intermediate potentials. Convexity and the definition of the ergodic averages
\[
X_N=\frac1N\sum_{k=1}^N x^k,\qquad
Y_N=\frac1N\sum_{k=1}^N y^k
\tag{109.17}
\]
then give a restricted primal–dual gap estimate
\[
\mathcal G_{B_X\times B_Y}(X_N,Y_N)
\le \frac{D(B_X,B_Y)}{N}.
\tag{109.18}
\]
Here \(B_X,B_Y\) are bounded test sets, and \(D\) depends on their distances from the initial point in the \(\tau^{-1}\) and \(\sigma^{-1}\) metrics. The gap is restricted because the full dual or primal domains may be unbounded, making a global supremum or infimum infinite.

More explicitly, for test sets on which the expression is well-defined, use
\[
\mathcal G_{B_X\times B_Y}(x,y)
=\sup_{\tilde y\in B_Y}L(x,\tilde y)
-\inf_{\tilde x\in B_X}L(\tilde x,y).
\tag{109.19}
\]
The theorem bounds this comparison gap by an initial-distance constant divided by \(N\); boundedness of \(B_X\) and \(B_Y\) makes that constant finite when measured from the initial iterates. Keeping the test sets in the notation matters both mathematically and in Lean: the theorem quantifies over comparison points, while a supremum over an entire unbounded domain may be infinite.

This is an ergodic statement about averages. It does not say that the final pair \((x^N,y^N)\) has gap \(O(1/N)\). If the primal and dual solutions are unique and the spaces finite-dimensional, the original analysis also establishes convergence of the iterates, but that is a separate conclusion from the averaged gap rate.


## 4. Two proximal examples

### 4.1 Sparse regression with an \(\ell_1\) penalty

Consider the Lasso objective
\[
\min_x \frac12\|Ax-b\|^2+\lambda\|x\|_1.
\tag{109.20}
\]
Choose \(K=A\), \(G(x)=\lambda\|x\|_1\), and
\(F(z)=\tfrac12\|z-b\|^2\). A direct conjugate calculation gives
\[
F^*(y)=\frac12\|y\|^2+\langle b,y\rangle.
\tag{109.21}
\]
The dual prox is
\[
\operatorname{prox}_{\sigma F^*}(v)
=\frac{v-\sigma b}{1+\sigma},
\tag{109.22}
\]
and the primal prox is soft thresholding:
\[
[\operatorname{prox}_{\tau G}(u)]_i
=\operatorname{sign}(u_i)\max(|u_i|-\tau\lambda,0).
\tag{109.23}
\]
Thus one PDHG iteration alternates a simple residual-space update with a sparse thresholding step, using \(A\) and \(A^*\). The adjoint identity is operationally important: implementations that use mismatched forward and adjoint discretizations are not implementing the stated saddle problem.

### 4.2 Total-variation denoising

For an image vector \(x\), noisy data \(b\), and discrete gradient \(K\), consider
\[
\min_x \frac12\|x-b\|^2+\lambda\|Kx\|_1.
\tag{109.24}
\]
Set \(G(x)=\tfrac12\|x-b\|^2\), \(F(z)=\lambda\|z\|_1\). Then \(F^*\) is the indicator of the coordinatewise box \(\|y\|_\infty\le\lambda\). The dual prox is coordinatewise clipping:
\[
[\operatorname{prox}_{\sigma F^*}(v)]_i
=\min(\lambda,\max(-\lambda,v_i)).
\tag{109.25}
\]
The primal prox is
\[
\operatorname{prox}_{\tau G}(u)=\frac{u+\tau b}{1+\tau}.
\tag{109.26}
\]
The method therefore alternates a gradient-like dual update followed by projection onto a box and a simple data-fidelity proximal step. In isotropic TV, the \(\ell_\infty\) box is replaced by a product of Euclidean balls, and each dual coordinate is projected onto its local ball.

These examples follow one design pattern: choose \(K\) to expose the structure in \(F(Kx)\), then select proximal maps that are cheap in their natural spaces. A good formalization keeps the general theorem independent of the specific soft-thresholding or clipping formula.

### 4.3 A scalar iteration by hand

The one-dimensional Lasso makes the update order visible without matrix notation. Take \(A=1\), \(b=2\), \(\lambda=\tfrac12\), and \(\tau=\sigma=\tfrac12\). Since \(\|A\|=1\), the step condition holds. Start at \(x^0=y^0=0\), with \(\bar x^0=x^0\). Formula (109.22) gives
\[
y^1=\frac{0+\frac12(0)-\frac12(2)}{1+\frac12}=-\frac23,
\qquad
x^1=\operatorname{soft}(0-\tfrac12 y^1,\tfrac14)=\frac1{12}.
\tag{109.27}
\]
The extrapolated value is \(\bar x^1=2x^1-x^0=\tfrac16\). Thus the next dual step must use \(\tfrac16\), not \(x^1=\tfrac1{12}\):
\[
y^2=\frac{y^1+\frac12\bar x^1-1}{1+\frac12}=-\frac{19}{18},
\qquad
x^2=\operatorname{soft}(x^1-\tfrac12 y^2,\tfrac14)=\frac{13}{36}.
\tag{109.28}
\]
The solution is \(x^*=\tfrac32\), \(y^*=-\tfrac12\). These values satisfy \(x^*-b=y^*\) and \(-y^*=\lambda\), so the KKT conditions hold. The early primal iterates need not resemble the solution closely; the example is for auditing the signs, thresholds, and use of the extrapolated state. It is also a compact regression fixture for a concrete implementation.


## 5. Lean proof architecture

### 5.1 Bundle the operator and its adjoint

Represent \(K\) as a continuous linear map between real inner-product spaces and use its adjoint for \(K^*\). Prove the identity
\(\langle Kx,y\rangle=\langle x,K^*y\rangle\) once. The algorithm, KKT conditions, and saddle function should all reuse this bundled map. An arbitrary pair of functions named forward and adjoint is not enough: the adjoint identity is one of the hypotheses that makes the proof telescope.

The operator norm theorem supplies
\(\|Kx\|\le\|K\|\|x\|\). The step condition (109.14) can then be established with a scalar quadratic inequality. This proof should be factored from the optimization argument so later preconditioned variants can replace the block-positivity lemma while reusing the proximal analysis.

A useful interface separates mathematical facts from the iteration state. One layer packages the continuous linear map and adjoint identity; another carries positive steps and a proof of the norm condition; a third exposes each proximal optimality certificate. The main theorem should receive these objects as assumptions and never inspect how an application computes \(Kx\). For a matrix implementation, that abstraction is what allows the same proof to cover sparse matrices, finite differences, and block operators.

### 5.2 Prove the prox inequality once

For any proper lower semicontinuous convex function, state prox optimality through the subgradient relation (109.7), then derive the three-point inequality (109.8). Apply the same abstract lemma to both \(G\) and \(F^*\). Avoid duplicating the proof with hand-expanded squared norms in each algorithm theorem.

The update is naturally a pure state transition:
\[
(x^k,y^k,\bar x^k)\longmapsto
(y^{k+1},x^{k+1},\bar x^{k+1}).
\]
A Lean structure can store the two prox certificates and the extrapolation equation. The convergence theorem consumes those certificates rather than unfolding the implementation of each prox.

### 5.3 Encode the ergodic theorem at the right level

First prove the one-step inequality for arbitrary comparison points \(x,y\). Then sum it over a finite range. Only after the telescope is complete should the proof introduce the averages \(X_N,Y_N\) and use convexity to move function values outside finite averages.

The restricted gap should be represented with explicit bounded comparison sets. This makes the finiteness assumptions visible and prevents a theorem from silently taking a supremum over an unbounded dual domain. The proof layers are:

~~~text
proximal optimality for F* and G
              |
              v
       one-step saddle inequality
              |
       step-size block positivity
              |
              v
       finite potential telescope
              |
              v
    convexity and ergodic averages
              |
              v
       restricted gap O(1/N)
~~~

The finite telescope is a good unit test for this architecture. Abstract away optimization and suppose a sequence of real quantities satisfies \(a_k\le p_k-p_{k+1}+c_k\). Summation yields \(\sum_{k<N}a_k\le p_0-p_N+\sum_{k<N}c_k\); nonnegativity of \(p_N\) then removes the final potential. The PDHG proof adds the saddle and convexity interpretation only after this algebraic fact is established. In Lean, use a finite sum over Fin N or an interval range N, state the index convention explicitly, and prove the identity by induction on N. This isolates the most common off-by-one error: the updates produce \(x^1,\ldots,x^N\), while the initial potential is indexed by \(0\).

The resulting theorem interface should say which points are averaged. If the one-step inequality compares \(x^{k+1}\) and \(y^{k+1}\), define both averages over indices \(1\) through \(N\); do not quietly average the initial state on one side. A small natural-number lemma aligning range N with the shifted update sequence can prevent a surprising amount of rewriting in the final proof.


## 6. Common failure modes

1. **Using \(K\) where \(K^*\) is required.** The primal update lives in the primal space and uses the adjoint.
2. **Reversing the update order.** The stated method updates the dual first, then the primal.
3. **Feeding the wrong point to the dual prox.** The dual update uses the extrapolated primal point.
4. **Treating extrapolation as a projection.** It is a linear combination and need not be feasible in an indicator-set formulation.
5. **Choosing steps independently.** The coupling term requires a condition involving \(\tau\sigma\|K\|^2\).
6. **Claiming a last-iterate gap rate from an ergodic theorem.** The \(O(1/N)\) result applies to averaged iterates and restricted comparison sets.
7. **Ignoring the properness assumptions.** The proximal minimizers and conjugate representation need proper lower semicontinuous convex functions.
8. **Dropping the operator adjoint identity.** The bilinear terms will not cancel or combine correctly.
9. **Confusing primal and dual indicator proxes.** A primal constraint projects \(x\); a dual norm constraint projects \(y\).
10. **Using the global gap when it may be infinite.** State bounded test sets or prove the full gap is finite.

## 7. Exercises

1. Derive the dual problem (109.4) from the saddle function.
2. Prove that the fixed points of (109.9) satisfy the KKT conditions (109.5).
3. Derive the three-point inequality (109.8) from proximal optimality.
4. Show that the block quadratic form in (109.13) is positive definite under (109.14).
5. Identify the cross term produced when the two proximal inequalities are added.
6. Derive the conjugate and dual proximal update for the Lasso example.
7. Verify the clipping and primal prox formulas for total-variation denoising.
8. State precisely why the restricted ergodic gap remains finite when the full dual domain is unbounded.
9. Prove the finite-sum identity that connects the one-step inequality to the averaged gap.
10. Design a Lean structure containing \(K\), \(K^*\), their adjoint identity, and an operator-norm bound.
11. Explain why an extrapolated point can be outside a primal constraint even though the new primal iterate is feasible.
12. Distinguish convergence of the averaged gap from convergence of the last iterate.

## 8. Chapter summary

PDHG solves a composite convex problem by alternating dual and primal proximal steps around a bounded linear coupling. The adjoint operator makes the KKT conditions explicit, while the extrapolated primal point improves the dual step. The condition \(\tau\sigma\|K\|^2<1\) controls the coupling through a positive block quadratic form.

Proximal optimality gives a one-step saddle inequality. Its potential terms telescope, and convexity converts the finite sum into an \(O(1/N)\) restricted gap bound for ergodic averages. In Lean, formalize adjoints, prox inequalities, block positivity, the deterministic telescope, and average convexity as separate lemmas. Keep the theorem’s output guarantee explicit: averaged gap, last-iterate gap, and iterate convergence are distinct conclusions.

## Further reading

- Chambolle and Pock, [“A First-Order Primal-Dual Algorithm for Convex Problems with Applications to Imaging”](https://doi.org/10.1007/s10851-010-0251-1), for the PDHG iteration and ergodic primal–dual gap analysis.
- Chapter 92, for projection and proximal maps.
- Chapter 108, for Fenchel duality and saddle-point certificates.

