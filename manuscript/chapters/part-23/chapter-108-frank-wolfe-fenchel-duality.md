# Chapter 108 — Frank–Wolfe, Fenchel Duality, and Saddle-Point Certificates

> **Audience.** This chapter assumes convex analysis and the Frank–Wolfe gap from Chapters 90 and 98, as well as the cached derivative table from Chapters 106–107. It explains how the LMO residual and Fenchel–Young residual combine into a primal–dual certificate.

Frank–Wolfe is often introduced as a geometric algorithm: compute a gradient, minimize a linear function over the feasible set, and move toward the resulting atom. For a finite sum with linear predictions, the same iteration also has a saddle-point interpretation. The gradient table is a collection of dual coordinates, the aggregate gradient is their linear image, and the LMO residual is one part of a primal–dual gap.

This viewpoint explains precisely what a gap estimate certifies. With an exact gradient, the Fenchel–Young residual vanishes, so the FW gap equals the full primal–dual gap. With a stale or approximate derivative table, the cached FW gap is only the feasible-set residual; the missing Fenchel–Young residual must also be accounted for before claiming a full primal–dual certificate.

## Learning objectives

After this chapter, you should be able to:

- derive the Fenchel dual of a linearly constrained prediction problem;
- decompose its primal–dual gap into a Fenchel–Young residual and an FW residual;
- show when the ordinary FW gap is exactly a primal–dual certificate;
- interpret the cached derivative refresh as a coordinate maximization in a saddle function;
- identify why a stochastic FW gap alone can understate the full duality gap;
- formalize the decomposition as reusable Lean lemmas.

## 1. A generalized linear objective and its conjugate

### 1.1 The separable prediction model

Let \(X\in\mathbb R^{n\times d}\), with rows \(a_i^\top\), and let \(\mathcal C\subseteq\mathbb R^d\) be a nonempty compact convex set. Suppose
\[
F(w)=\psi(Xw),\qquad
\psi(z)=\frac1n\sum_{i=1}^n\phi_i(z_i),
\tag{108.1}
\]
where each \(\phi_i:\mathbb R\to\mathbb R\) is proper, closed, and convex. In this chapter assume the losses are differentiable wherever a gradient is used. The constrained primal value is
\[
P(w)=\psi(Xw),\qquad w\in\mathcal C.
\tag{108.2}
\]

For a proper convex function \(\psi\), its Fenchel conjugate is
\[
\psi^*(\alpha)=\sup_{z\in\mathbb R^n}
\{\langle\alpha,z\rangle-\psi(z)\}.
\tag{108.3}
\]
The Fenchel–Young inequality states
\[
\psi(z)+\psi^*(\alpha)\ge\langle\alpha,z\rangle.
\tag{108.4}
\]
Equality holds exactly when \(\alpha\in\partial\psi(z)\); for differentiable \(\psi\), this is \(\alpha=\nabla\psi(z)\).

The conjugate has an especially simple form for the separable average:
\[
\psi^*(\alpha)=\frac1n\sum_{i=1}^n\phi_i^*(n\alpha_i).
\tag{108.5}
\]
To see the scaling, separate the supremum coordinatewise:
\[
\sup_{z_i}\left\{\alpha_i z_i-\frac1n\phi_i(z_i)\right\}
=\frac1n\sup_{z_i}\{(n\alpha_i)z_i-\phi_i(z_i)\}.
\]
The factor \(n\) inside each component conjugate is essential. It matches the cached derivative convention
\(\alpha_i=\phi_i'(a_i^\top w)/n\).

### 1.2 The saddle function and dual objective

The conjugate representation gives
\[
\psi(Xw)=\sup_{\alpha\in\mathbb R^n}
\{\langle\alpha,Xw\rangle-\psi^*(\alpha)\}.
\tag{108.6}
\]
Define the saddle function
\[
\mathcal L(w,\alpha)
=\langle\alpha,Xw\rangle-\psi^*(\alpha),
\qquad w\in\mathcal C.
\tag{108.7}
\]
Then the primal problem is \(\min_{w\in\mathcal C}\sup_\alpha\mathcal L(w,\alpha)\). The corresponding dual objective is
\[
D(\alpha)=\inf_{u\in\mathcal C}\mathcal L(u,\alpha)
=-\psi^*(\alpha)-\sigma_{\mathcal C}(-X^\top\alpha),
\tag{108.8}
\]
where \(\sigma_{\mathcal C}(q)=\sup_{u\in\mathcal C}\langle q,u\rangle\) is the support function.

Weak duality follows directly: for every feasible \(w\) and every \(\alpha\),
\[
D(\alpha)\le \mathcal L(w,\alpha)\le P(w).
\tag{108.9}
\]
The first inequality uses the infimum in (108.8); the second uses the conjugate representation (108.6). This argument needs no strong-duality theorem.

Because \(\mathcal C\) is compact and the inner objective is linear, the infimum in (108.8) is attained for each fixed \(\alpha\). This does not by itself prove that the supremum over \(\alpha\) is attained. The gradient-at-an-optimum argument below supplies a concrete dual optimizer when the primal minimizer exists and the stated differentiability and convexity assumptions hold. This is often a cleaner proof than invoking a general minimax theorem, and it makes the certificate-producing dual vector explicit.

When \(w^\star\) minimizes a differentiable convex primal objective, set
\(\alpha^\star=\nabla\psi(Xw^\star)\). Fenchel–Young equality gives
\(P(w^\star)=\mathcal L(w^\star,\alpha^\star)\). The constrained first-order condition says \(w^\star\) minimizes
\(\langle X^\top\alpha^\star,u\rangle\) on \(\mathcal C\), so
\(\mathcal L(w^\star,\alpha^\star)=D(\alpha^\star)\). Thus the primal and dual values agree at this pair. The proof uses both tangent equality and constrained optimality; neither one alone is enough.


## 2. Decompose the primal–dual gap

### 2.1 Two nonnegative residuals

For feasible \(w\) and any dual vector \(\alpha\), subtract the dual value from the primal value:
\[
\begin{aligned}
P(w)-D(\alpha)
&=\psi(Xw)+\psi^*(\alpha)+\sigma_{\mathcal C}(-X^\top\alpha)\\
&=\underbrace{\psi(Xw)+\psi^*(\alpha)
-\langle\alpha,Xw\rangle}_{R_{\mathrm{FY}}(w,\alpha)}
+\underbrace{\langle\alpha,Xw\rangle+
\sigma_{\mathcal C}(-X^\top\alpha)}_{R_{\mathrm{FW}}(w,\alpha)}.
\end{aligned}
\tag{108.10}
\]
The first term \(R_{\mathrm{FY}}\) is the Fenchel–Young residual. It is nonnegative by (108.4), and it vanishes exactly when \(\alpha\in\partial\psi(Xw)\).

The second term is
\[
R_{\mathrm{FW}}(w,\alpha)
=\max_{s\in\mathcal C}\langle\alpha,X(w-s)\rangle.
\tag{108.11}
\]
It is nonnegative because \(s=w\) is allowed. It is the Frank–Wolfe gap formed with the parameter-space vector \(X^\top\alpha\). Equation (108.10) is an exact identity:
\[
\boxed{\text{primal--dual gap}
=\text{Fenchel--Young residual}
+\text{linear-oracle residual}.}
\]

This decomposition separates two distinct questions. Does the dual vector describe a supporting hyperplane to the loss at the current prediction? That is measured by \(R_{\mathrm{FY}}\). Does the current point minimize the linear function induced by that dual vector over the feasible set? That is measured by \(R_{\mathrm{FW}}\).

### 2.2 When the FW gap is the whole certificate

Take the exact dual vector
\(\alpha_w=\nabla\psi(Xw)\). By Fenchel–Young equality,
\(R_{\mathrm{FY}}(w,\alpha_w)=0\). Therefore
\[
P(w)-D(\alpha_w)
=R_{\mathrm{FW}}(w,\alpha_w)
=\max_{s\in\mathcal C}
\langle\nabla F(w),w-s\rangle
=G(w).
\tag{108.12}
\]
For convex \(F\), the FW gap is thus a primal–dual gap for the matched pair \((w,\alpha_w)\), and it bounds primal suboptimality.

This equality is a stronger explanation of the familiar convexity bound. The primal point contributes a feasible primal value; the exact gradient generates a dual vector with zero Fenchel residual; the LMO gap then measures the entire primal–dual discrepancy.

### 2.3 What an approximate gradient gap omits

Now use a cached derivative vector \(\alpha\ne\nabla\psi(Xw)\). The quantity produced by the cached LMO is still
\(R_{\mathrm{FW}}(w,\alpha)\), but (108.10) gives
\[
P(w)-D(\alpha)
=R_{\mathrm{FY}}(w,\alpha)+R_{\mathrm{FW}}(w,\alpha)
\ge R_{\mathrm{FW}}(w,\alpha).
\tag{108.13}
\]
The cached gap is a lower bound on the full primal–dual gap, not an upper bound. A small cached gap can coexist with a large Fenchel–Young residual, so it cannot by itself certify that the primal objective is close to optimality.

Chapter 106 established a different relation: its stale-table error bounds the difference between the cached gap and the true FW gap. That estimate is useful, but it does not remove the Fenchel residual in a primal–dual certificate. The two error questions should not be conflated:

- table error controls how well the cached linear functional approximates the true gradient functional;
- Fenchel–Young residual controls whether the chosen dual vector supports the loss at the current prediction.

A formal proof or a solver report should name which certificate is being returned: true FW gap, cached FW gap, Fenchel residual, or full primal–dual gap.

### 2.4 Turn the decomposition into an objective certificate

Let \(P^\star=\min_{u\in\mathcal C}P(u)\). Weak duality gives \(D(\alpha)\le P^\star\), so (108.10) implies
\[
P(w)-P^\star
\le P(w)-D(\alpha)
=R_{\mathrm{FY}}(w,\alpha)+R_{\mathrm{FW}}(w,\alpha).
\tag{108.14}
\]
Thus an upper bound on both residuals is an objective-error certificate. An upper bound on only the cached FW residual is not enough. This is a useful API boundary for optimization software: a routine may return the LMO residual cheaply, while a separate routine evaluates or bounds the Fenchel residual.

The two residuals also require different mathematical information. The LMO residual depends on the feasible set and the dual linear form. The Fenchel residual depends on the loss and the compatibility of its derivative with the cached dual vector. Under stronger curvature assumptions, the Fenchel residual can sometimes be bounded by a norm of \(\alpha-\nabla\psi(Xw)\); that estimate is separate from the diameter bound in Chapter 106 and may not hold for a merely convex loss.

~~~text
primal value P(w)                         dual value D(alpha)
       |                                           |
       +---------- primal-dual difference --------+
                           |
              +------------+------------+
              |                         |
              v                         v
       Fenchel-Young residual      FW linear residual
       loss / dual mismatch        feasible-set / LMO
              |                         |
              +------------+------------+
                           |
                           v
              full primal-dual certificate
~~~


## 3. Coordinate refresh as a saddle update

### 3.1 Maximize one dual coordinate at the current prediction

For the separable average, the saddle function can be written
\[
\mathcal L(w,\alpha)
=\frac1n\sum_{i=1}^n
\left(n\alpha_i\,a_i^\top w-\phi_i^*(n\alpha_i)\right).
\tag{108.15}
\]
Fix \(w\) and all coordinates except \(\alpha_i\). Maximizing over \(\alpha_i\) is equivalent, after the change of variable \(\beta_i=n\alpha_i\), to
\[
\frac1n\sup_{\beta_i}
\{\beta_i\,a_i^\top w-\phi_i^*(\beta_i)\}
=\frac1n\phi_i(a_i^\top w).
\tag{108.16}
\]
If \(\phi_i\) is differentiable, the maximizing coordinate is
\[
\alpha_i=\frac1n\phi_i'(a_i^\top w).
\tag{108.17}
\]
Thus the one-coordinate refresh in Chapter 106 is an exact block maximization of the saddle function at the current primal point.

This interpretation explains why the table is useful without implying that it is unbiased. Each refresh makes one coordinate dual-optimal for the current prediction; other coordinates remain optimal for older predictions. The aggregate \(r=X^\top\alpha\) is exactly the primal linear functional induced by the current dual table, even though that table may not be globally optimal for the current \(w\).

### 3.2 The primal move is conditional-gradient minimization

For a fixed \(\alpha\), minimizing the saddle function over \(w\in\mathcal C\) is equivalent to minimizing
\[
\langle X^\top\alpha,w\rangle.
\tag{108.18}
\]
The LMO therefore computes a minimizer of the primal variable for the current dual vector. A Frank–Wolfe convex combination moves toward that minimizer while preserving feasibility.

The stochastic algorithm alternates two partial operations:

1. maximize one dual coordinate at the current primal point;
2. take a conditional-gradient step in the primal variable for the refreshed dual table.

It is not a full maximization over all dual coordinates followed by an exact primal minimization. Nor does this viewpoint alone prove that the primal–dual objective improves monotonically each iteration. The convergence proof still needs the stale-table recurrence and the smoothness descent estimate from Chapters 106–107.


## 4. Two worked examples

### 4.1 Exact and inexact certificates for a scalar quadratic

Let
\[
\psi(z)=\tfrac12 z^2,\qquad X=1,\qquad\mathcal C=[-1,1],\qquad w=1.
\tag{108.19}
\]
The conjugate is \(\psi^*(\alpha)=\tfrac12\alpha^2\), and the primal value is \(P(1)=1/2\).

With the exact dual vector \(\alpha=1=\psi'(1)\), the dual value is
\[
D(1)=-\tfrac12-\sigma_{[-1,1]}(-1)
=-\tfrac12-1=-\tfrac32.
\]
The full primal–dual gap is \(P-D=2\). The FW gap is
\(\max_{s\in[-1,1]}(1-s)=2\), and the Fenchel residual is zero.

Now use an inexact table value \(\alpha=1/2\). The dual value is
\[
D(1/2)=-\tfrac18-\sigma_{[-1,1]}(-1/2)
=-\tfrac18-\tfrac12=-\tfrac58.
\]
The primal–dual gap is \(1/2+5/8=9/8\). Its two parts are
\[
R_{\mathrm{FY}}=\tfrac12+\tfrac18-\tfrac12=\tfrac18,
\qquad
R_{\mathrm{FW}}=\max_{s\in[-1,1]}\tfrac12(1-s)=1.
\tag{108.20}
\]
They add to \(9/8\). The true FW gap is \(2\), while the cached gap is \(1\). The inexact vector produces a valid dual lower bound, but the cached gap alone is not the primal–dual gap.

### 4.2 Scaling in a two-example conjugate

Take \(n=2\),
\[
\phi_1(z)=\tfrac12(z-1)^2,\qquad
\phi_2(z)=\tfrac12(z+1)^2,\qquad z=(0,0).
\tag{108.21}
\]
Then \(\nabla\psi(z)=(-1/2,1/2)\), and \(\psi(z)=1/2\). The scalar conjugates are
\[
\phi_1^*(\beta)=\beta+\tfrac12\beta^2,\qquad
\phi_2^*(\beta)=-\beta+\tfrac12\beta^2.
\tag{108.22}
\]
Using the scaled formula (108.5), evaluate at \(\alpha=(-1/2,1/2)\):
\[
\psi^*(\alpha)
=\tfrac12\left(\phi_1^*(-1)+\phi_2^*(1)\right)
=\tfrac12\left(-\tfrac12-\tfrac12\right)
=-\tfrac12.
\tag{108.23}
\]
Since \(\langle\alpha,z\rangle=0\), the Fenchel residual is
\(1/2-1/2=0\), as it must be for the exact gradient. Omitting the factor \(n\) inside (108.5) would give the wrong conjugate and break this equality.


## 5. Lean proof architecture

### 5.1 Define the certificate components first

A formalization can define four quantities independently:

- primal value \(P(w)=\psi(Xw)\);
- dual value \(D(\alpha)=-\psi^*(\alpha)-\sigma_{\mathcal C}(-X^\top\alpha)\);
- Fenchel–Young residual \(R_{\mathrm{FY}}\);
- linear-oracle residual \(R_{\mathrm{FW}}\).

Then prove an algebraic identity \(P(w)-D(\alpha)=R_{\mathrm{FY}}+R_{\mathrm{FW}}\). This identity needs only definitions and the support-function expression for the infimum over the feasible set. Prove nonnegativity of each term in separate lemmas: Fenchel–Young inequality for the first, feasibility of \(w\) for the second.

The exact-gradient theorem is then short. Substitute \(\alpha=\nabla\psi(Xw)\), use Fenchel–Young equality to eliminate \(R_{\mathrm{FY}}\), and identify \(R_{\mathrm{FW}}\) with the ordinary FW gap by the chain rule.

### 5.2 Keep finite-sum conjugacy separate

For (108.5), unfold the finite sum and split a supremum over a product into coordinatewise suprema. It is useful to prove the scalar scaling identity
\[
\sup_z\left(\alpha z-\frac1n\phi(z)\right)
=\frac1n\phi^*(n\alpha)
\tag{108.24}
\]
first. A finite-product lemma can then assemble the coordinates. This proof should not mention a data matrix, feasible set, or LMO; it is a reusable fact about separable functions.

### 5.3 State what the stochastic gap proves

The approximate-table theorem should state both facts:
\[
R_{\mathrm{FW}}(w,\alpha)\le P(w)-D(\alpha),
\]
and
\[
|R_{\mathrm{FW}}(w,\alpha)-G(w)|
\le D_\infty\|\alpha-\nabla\psi(Xw)\|_1.
\tag{108.25}
\]
The first is a duality identity and nonnegativity result. The second is the geometric perturbation theorem from Chapter 106. Neither implies that the cached FW gap alone is an upper bound on the primal objective error. To obtain such a certificate, formalize an upper bound on the Fenchel–Young residual as well.

For the saddle interpretation, prove a coordinate optimality lemma at fixed \(w\), then separately prove the aggregate-update invariant \(r=X^\top\alpha\). Avoid putting differentiability, coordinate maximization, table update, and duality-gap decomposition into one theorem. Each has a different mathematical dependency and is useful on its own.


## 6. Common failure modes

1. **Dropping the scaling in the conjugate.** Averaging \(n\) losses puts \(n\alpha_i\) inside \(\phi_i^*\).
2. **Calling the cached FW gap the full duality gap.** It omits the Fenchel–Young residual.
3. **Using weak duality in the wrong direction.** Every dual value is a lower bound on every feasible primal value.
4. **Assuming strong duality without a pair argument or theorem.** Weak duality is immediate; equality requires additional structure.
5. **Confusing a supporting slope with a stale slope.** Fenchel equality requires \(\alpha\in\partial\psi(Xw)\).
6. **Claiming each coordinate refresh makes the full vector unbiased.** It makes one coordinate exact; the others remain stale.
7. **Assuming saddle updates are automatically monotone.** The alternating interpretation motivates the algorithm but does not replace its convergence proof.
8. **Forgetting that the support function uses \(-X^\top\alpha\).** The sign follows from converting a minimum to a negative maximum.
9. **Treating a lower bound on the duality gap as an optimality upper bound.** A small component of a nonnegative sum does not bound the sum.
10. **Mixing the two errors.** The table-to-gradient error and the Fenchel–Young residual are related but distinct quantities.

## 7. Exercises

1. Derive the dual objective (108.8) from the saddle function and the support function.
2. Prove weak duality (108.9) without invoking a minimax theorem.
3. Expand the algebra leading to the decomposition (108.10).
4. Show that \(R_{\mathrm{FW}}(w,\alpha)\ge0\) by choosing \(s=w\).
5. Prove that the exact gradient makes the Fenchel–Young residual vanish.
6. For \(n\) separable losses, derive the scaled conjugate formula (108.5).
7. Recompute the scalar quadratic example when \(\alpha=0\). Compare its dual value, Fenchel residual, and cached gap.
8. State conditions under which a primal optimizer and its gradient form a primal–dual optimal pair.
9. Explain why one-coordinate maximization does not imply that the complete dual objective increases at every stochastic iteration.
10. Design Lean definitions for the primal–dual gap and its two residual terms.
11. Prove the scalar conjugate scaling identity (108.24), then identify the finite-product theorem needed to obtain (108.5).
12. Explain how a certified upper bound on both residual terms would yield an objective-error certificate.

## 8. Chapter summary

Fenchel duality reveals that an FW gap has a precise primal–dual meaning. For an exact gradient, Fenchel–Young equality makes its residual zero, so the true FW gap equals the full primal–dual gap. For a stale derivative table, the cached FW gap is only the feasible-set residual; the Fenchel–Young residual is an additional nonnegative term.

In generalized linear finite sums, the derivative table is a dual-coordinate state. Refreshing one coordinate exactly maximizes the saddle function in that coordinate, and the aggregate \(X^\top\alpha\) supplies the LMO direction. This interpretation explains the algorithm without claiming that the cached table is unbiased or that the saddle objective decreases monotonically. In Lean, make the duality identity, residual nonnegativity, exact-gradient equality, coordinate update, and stale-gradient error separate results.

## Further reading

- Negiar et al., [“Stochastic Frank-Wolfe for Constrained Finite-Sum Minimization”](https://proceedings.mlr.press/v119/negiar20a.html), for the primal–dual saddle view motivating the generalized-linear cached-gradient algorithm.
- Chapters 90, 98, 105, and 106, for convex optimality, FW gaps, stochastic estimators, and structured derivative tables.

