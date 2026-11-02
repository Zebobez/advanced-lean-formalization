# Chapter 115 — Variable-Metric Forward–Backward Splitting

> **Audience.** This chapter extends the forward–backward method of Chapter 113 from Euclidean steps to preconditioned steps. It focuses on the geometry behind a positive-definite metric, the weighted proximal map, and the summable variation condition that permits the metric to change between iterations.

A scalar step size shortens or lengthens every direction equally. Many problems have very different curvature in different coordinates, so a scalar step must be chosen for the most restrictive direction. Preconditioning replaces the scalar step by a positive-definite linear map. The resulting step can move farther in flat directions while respecting steep ones.

Changing the geometry also changes the proof. With one fixed metric, the usual Fejér distance is simply measured in a weighted norm. With a sequence of metrics, the distance itself changes after each step and no longer telescopes automatically. A controlled, summable metric variation supplies the missing comparison.

## Learning objectives

After this chapter, you should be able to:

- define a weighted inner product and proximal map from a positive-definite operator;
- derive the preconditioned forward–backward update;
- express cocoercivity and step-size bounds in the weighted geometry;
- explain why changing metrics requires a quasi-Fejér estimate;
- verify uniform positivity and summable variation for a metric sequence;
- structure Lean proofs around operator order, inverse metrics, and transition certificates.

## 1. Geometry from a positive operator

### 1.1 Weighted inner products

Let \(H\) be a real Hilbert space and let \(U:H\to H\) be bounded, self-adjoint, and strongly positive: for some \(\alpha>0\),
\[
\langle Ux,x\rangle\ge\alpha\|x\|^2
\quad\text{for every }x\in H.
\tag{115.1}
\]
Then \(U\) is invertible. It induces a weighted inner product and norm
\[
\langle x,y\rangle_{U^{-1}}:=\langle U^{-1}x,y\rangle,
\qquad
\|x\|_{U^{-1}}^2:=\langle U^{-1}x,x\rangle.
\tag{115.2}
\]
The notation uses \(U^{-1}\) in the inner product because \(U\) will multiply the forward gradient. If \(U\) is diagonal with entries \(u_i>0\), then the squared metric length of \(x\) is \(\sum_i x_i^2/u_i\).

The operator \(U\) is the preconditioner: it maps a gradient vector to a direction. Strong positivity prevents a direction from being discarded, while an upper bound \(\|U\|\le\mu\) controls how much the map can amplify the forward operator.

### 1.2 The metric proximal map

For a proper lower-semicontinuous convex function \(g\), define the metric proximal map by
\[
\operatorname{prox}^{U^{-1}}_{\gamma g}(v)
=\arg\min_y\left\{g(y)+\frac{1}{2\gamma}\|y-v\|_{U^{-1}}^2\right\}.
\tag{115.3}
\]
The optimality condition is
\[
\frac{1}{\gamma}U^{-1}(v-y)\in\partial g(y).
\tag{115.4}
\]
Equivalently, this map is the resolvent \(J_{\gamma U\partial g}\). For \(U=I\), (115.3) is the ordinary proximal map. For diagonal \(U\) and separable \(g\), it often remains coordinatewise computable; for a dense matrix \(U\), the metric proximal subproblem can become the dominant cost.

The metric is therefore not an automatic improvement. It is useful when it reduces the effective curvature and the weighted proximal map stays tractable.

### 1.3 A change of coordinates

For a fixed \(U\), the weighted geometry can be understood as ordinary Euclidean geometry after a linear change of variables. In finite dimensions, set \(z=U^{-1/2}x\), so \(x=U^{1/2}z\). Then \(\|x-y\|_{U^{-1}}=\|U^{-1/2}(x-y)\|\), and the metric proximal problem becomes an ordinary proximal problem for the transformed function \(z\mapsto g(U^{1/2}z)\). The preconditioned gradient direction is exactly the gradient direction of the transformed smooth function in \(z\)-coordinates.

This interpretation explains both the benefit and the cost. A good \(U\) balances curvature in the transformed coordinates. A poor \(U\) can make the transformed objective more ill-conditioned, and a changing \(U_k\) means the algorithm effectively changes coordinates between iterations. The quasi-Fejér condition is the proof obligation that keeps those coordinate systems comparable.

## 2. Preconditioned forward–backward steps

### 2.1 The update and its inclusion certificate

Consider the inclusion \(0\in Ax+Bx\), where \(A\) is maximal monotone and \(B:H\to H\) is \(\beta\)-cocoercive in the original Hilbert geometry. Given a positive operator \(U_k\) and a fixed \(\gamma>0\), define
\[
x^{k+1}
=J_{\gamma U_k A}\bigl(x^k-\gamma U_k Bx^k\bigr).
\tag{115.5}
\]
The explicit part applies the preconditioner to \(Bx^k\); the implicit part uses the resolvent associated with the same preconditioner.

For a fixed \(U\), a point \(x\) is a fixed point of the corresponding map exactly when
\[
x=J_{\gamma U A}(x-\gamma UBx)
\quad\Longleftrightarrow\quad
-Bx\in Ax.
\tag{115.6}
\]
Indeed, the resolvent certificate gives \(-\gamma UBx\in\gamma UAx\). Since \(U\) is invertible, this is equivalent to the original inclusion. Thus preconditioning changes the path to a solution without changing the solution set.

When \(A=\partial g\) and \(B=\nabla f\), (115.5) takes the minimization form
\[
x^{k+1}
=\operatorname{prox}^{U_k^{-1}}_{\gamma g}
\bigl(x^k-\gamma U_k\nabla f(x^k)\bigr).
\tag{115.7}
\]
The forward and backward operations must use compatible geometry. Applying \(U_k\) only to the gradient while retaining a Euclidean proximal map would define a different algorithm.

### 2.2 Cocoercivity in the weighted geometry

For a fixed self-adjoint positive \(U\), the transformed forward map \(UB\) is cocoercive in the \(U^{-1}\)-inner product. For \(e=Bx-By\),
\[
\begin{aligned}
\langle Ue,x-y\rangle_{U^{-1}}
&=\langle e,x-y\rangle\\
&\ge\beta\|e\|^2\\
&\ge\frac{\beta}{\|U\|}\|Ue\|_{U^{-1}}^2.
\end{aligned}
\tag{115.8}
\]
The last inequality uses \(\|Ue\|_{U^{-1}}^2=\langle Ue,e\rangle\le\|U\|\|e\|^2\). Thus \(UB\) is at least \(\beta/\|U\|\)-cocoercive in the weighted geometry. If \(\|U_k\|\le\mu\) uniformly, the common conservative step-size range is
\[
0<\gamma<\frac{2\beta}{\mu}.
\tag{115.9}
\]
For a convex function with an \(L\)-Lipschitz gradient, \(\beta=1/L\), so the bound becomes \(0<\gamma<2/(L\mu)\). A well-chosen metric can make \(\mu\) much smaller than the effective unpreconditioned curvature in the directions that dominate the iteration.

This estimate is sufficient, not necessarily sharp. If the preconditioner and Hessian structure are known, a direct weighted smoothness or cocoercivity estimate can give a less conservative condition.

For a twice differentiable objective in finite dimensions, a useful direct condition is
\[
\nabla^2 f(x)\preceq L_U U^{-1}
\quad\text{for every }x.
\tag{115.10}
\]
Taylor's theorem then bounds the quadratic remainder by \(L_U\|y-x\|_{U^{-1}}^2/2\). A metric proximal-gradient model with \(\gamma\le1/L_U\) majorizes \(f\), just as the Euclidean model in Chapter 114 does. This direction-sensitive bound can be much better than substituting a global Euclidean \(L\) and the crude operator norm \(\|U\|\).

## 3. What changes when the metric varies

### 3.1 Uniform bounds and controlled variation

Let \((U_k)\) be a sequence of bounded self-adjoint operators with uniform positivity and bounded norm:
\[
\alpha I\preceq U_k,\qquad \|U_k\|\le\mu
\quad\text{for every }k,
\tag{115.11}
\]
where \(\alpha>0\) and \(\mu<+\infty\). The notation \(S\preceq T\) means \(\langle Sx,x\rangle\le\langle Tx,x\rangle\) for every \(x\).

The changing metrics must also vary slowly enough. A standard sufficient condition is that there be a summable nonnegative sequence \((\eta_k)\) with
\[
(1+\eta_k)U_{k+1}\succeq U_k,
\qquad
\sum_{k=0}^{\infty}\eta_k<+\infty.
\tag{115.12}
\]
This allows the preconditioner to improve or fluctuate, but it prevents its positive directions from shrinking by a fixed amount forever. Inverting the order relation gives
\[
\|v\|_{U_{k+1}^{-1}}^2
\le(1+\eta_k)\|v\|_{U_k^{-1}}^2.
\tag{115.13}
\]
The sum of the drift terms is finite, so a one-step contraction measured using \(U_k^{-1}\) remains a quasi-Fejér estimate when the next distance is measured using \(U_{k+1}^{-1}\).

### 3.2 A convergence theorem

Suppose \(A\) is maximal monotone, \(B\) is \(\beta\)-cocoercive, and the solution set \(\operatorname{zer}(A+B)\) is nonempty. Assume (115.11)–(115.12), and select \(\gamma\) with a strict uniform margin inside (115.9). Then the exact iteration (115.5) converges weakly to a solution. In finite dimensions, this is norm convergence.

This statement is a simplified error-free, unrelaxed specialization of the variable-metric forward–backward theorem of Combettes and Vũ. Their more general result permits bounded relaxation parameters and summable errors in the forward and backward steps. It also identifies additional conditions that upgrade weak convergence to strong convergence in infinite-dimensional spaces.

For a fixed \(U_k=U\), condition (115.12) holds with \(\eta_k=0\); ordinary Fejér monotonicity in the \(U^{-1}\)-norm drives the proof. With variable \(U_k\), (115.13) adds a multiplicative drift. Summability is what lets that drift accumulate to a finite factor rather than erasing the contraction.

The convergence statement is qualitative. Bounded positive metrics and weak convergence do not by themselves supply a uniform objective-gap rate. A rate requires a potential inequality and assumptions that control how the changing metric enters its telescope.

### 3.3 The quasi-Fejér calculation

The role of the variation condition becomes clearer at the level of one step. A strict uniform margin in the step-size bound and the uniform metric bounds give a common averagedness constant for the maps measured in their respective weighted Hilbert spaces. Therefore, for any solution \(z\), there is a constant \(c>0\), independent of \(k\), such that
\[
\|x^{k+1}-z\|_{U_k^{-1}}^2
+c\|x^{k+1}-x^k\|_{U_k^{-1}}^2
\le\|x^k-z\|_{U_k^{-1}}^2.
\tag{115.14}
\]
This is a Fejér decrease, but only in the current metric. Apply (115.13) to the next iterate's distance from \(z\):
\[
\|x^{k+1}-z\|_{U_{k+1}^{-1}}^2
\le(1+\eta_k)\left(
\|x^k-z\|_{U_k^{-1}}^2
-c\|x^{k+1}-x^k\|_{U_k^{-1}}^2\right).
\tag{115.15}
\]
Because \(\sum_k\eta_k\) is finite, the product of the factors \(1+\eta_k\) is bounded. The standard quasi-Fejér argument then bounds the distance sequence and controls the accumulated step residuals. Maximal monotonicity identifies weak cluster points with zeros of \(A+B\); the Hilbert-space weak-convergence argument shows the sequence has a single weak limit.

This derivation explains why an arbitrary sequence of positive-definite matrices is not enough. Positivity gives a norm at each iteration, but the comparison between consecutive norms is the invariant that lets one convergence proof span all iterations.

## 4. Worked examples

### 4.1 Diagonal scaling solves a separable quadratic exactly

Let
\[
f(x)=\frac12\sum_{i=1}^n a_i(x_i-b_i)^2,
\qquad
g(x)=\lambda\|x\|_1,
\qquad a_i>0.
\tag{115.16}
\]
The gradient is \((a_i(x_i-b_i))_i\). Choose the fixed preconditioner \(U=\operatorname{diag}(1/a_i)\) and \(\gamma=1\). The forward point is \(b\), independent of the current iterate:
\[
x-U\nabla f(x)=b.
\tag{115.17}
\]
The metric proximal map separates by coordinate. In coordinate \(i\), its objective is \(\lambda|y_i|+\tfrac12a_i(y_i-b_i)^2\), so
\[
\bigl(\operatorname{prox}^{U^{-1}}_{g}(b)\bigr)_i
=\operatorname{soft}_{\lambda/a_i}(b_i).
\tag{115.18}
\]
This is exactly the minimizer of each summand in \(f+g\). The chosen metric removes the quadratic scaling from the forward step and makes the method reach the solution in one iteration.

This example is deliberately favorable: \(f\) is diagonal quadratic and \(g\) is separable in the same coordinates. If \(g\) couples coordinates, the diagonal metric proximal map may not split, even though the gradient update is cheap.

### 4.2 A slowly varying metric on an anisotropic quadratic

Take \(f(x)=\tfrac12(x_1^2+9x_2^2)\), \(g=0\), and
\[
U_k=\operatorname{diag}\left(1,1+\frac{1}{k+1}\right),
\qquad
\eta_k=\frac{1}{(k+1)(k+3)}.
\tag{115.19}
\]
The eigenvalues of \(U_k\) lie in \([1,2]\), and direct multiplication verifies \((1+\eta_k)U_{k+1}=U_k\). The drift sequence is summable. Here \(\nabla f\) is \(9\)-Lipschitz, so \(\beta=1/9\), and \(\|U_k\|\le2\). The choice \(\gamma=1/20\) lies strictly below \(2\beta/2=1/9\).

From \(x^0=(1,1)\), the first two iterates are
\[
x^1=(0.95,0.1),
\qquad
x^2=(0.9025,0.0325).
\tag{115.20}
\]
The second coordinate contracts quickly because its metric weight initially doubles the forward action in that high-curvature direction. The preconditioner then drifts back toward the identity while satisfying the summable-variation condition. Since the optimum is \(0\) and the space is finite-dimensional, the convergence theorem yields norm convergence.

## 5. Lean proof architecture

### 5.1 Encode operator order and metric norms

Represent \(U\) as a linear continuous map with fields for self-adjointness and a lower bound \(\alpha I\preceq U\). In finite dimension, positive definiteness provides invertibility; in an abstract Hilbert-space development, make the inverse or its existence theorem an explicit interface. Define the weighted inner product using \(U^{-1}\), then prove the norm laws once.

Do not encode \(S\preceq T\) as an informal matrix intuition. Define it by the quadratic-form condition
\[
S\preceq T
\quad\Longleftrightarrow\quad
\forall x,\ \langle Sx,x\rangle\le\langle Tx,x\rangle.
\tag{115.21}
\]
This representation makes positivity, transitivity, and the metric-drift hypothesis available as reusable lemmas.

### 5.2 Separate the fixed-metric step from the changing-metric estimate

First prove, for one positive \(U\), that the transformed resolvent is firmly nonexpansive in the \(U^{-1}\)-inner product and that the transformed forward step is averaged under (115.9). Then prove the fixed-point equivalence (115.6) from the resolvent graph certificate.

For the variable sequence, retain \(U_k\) in the transition record. Prove the one-step Fejér estimate in metric \(U_k^{-1}\), then apply the inverse-order lemma to move the left side to metric \(U_{k+1}^{-1}\). The summable scalar sequence \(\eta_k\) belongs in this second proof layer; it should not be mixed into the fixed-metric averagedness theorem.

This organization localizes the main formal difficulty. The operator algebra is the same at every iteration; what changes is the potential used to compare errors to a solution. A finite-sum or quasi-Fejér lemma can then consume the transition estimates and the summability proof.

### 5.3 Track the geometry in certificates

A useful transition certificate contains the current state, the metric, the preconditioned forward point, the next proximal point, and witnesses for the resolvent inclusion. The convergence theorem additionally consumes uniform positivity, a common norm bound, a summable drift sequence, and a step-size margin.

Keeping these fields explicit prevents a common elaboration problem: an inequality in \(\|\cdot\|_{U_k^{-1}}\) cannot be simplified by Euclidean norm lemmas until the metric is fixed or related to the identity by its eigenvalue bounds. Prove those comparison lemmas explicitly and invoke them at the boundary where the proof changes geometry.

## 6. Failure modes and extensions

1. **Preconditioning only the forward map.** The metric proximal map must match the operator used in the resolvent.
2. **Forgetting invertibility.** The fixed-point equivalence uses strong positivity to cancel \(U\).
3. **Using the Euclidean step bound unchanged.** The transformed cocoercivity modulus depends on the operator norm of \(U\).
4. **Claiming Fejér monotonicity across changing metrics.** One obtains quasi-Fejér control with a drift term; direct telescoping needs (115.12) or another comparison.
5. **Allowing unbounded or degenerate metrics.** Uniform upper and lower bounds are part of the stated theorem.
6. **Treating \(\sum\eta_k<\infty\) as optional.** Persistent metric drift can overwhelm the contraction estimate.
7. **Assuming a weighted proximal map stays easy.** A dense metric can destroy separability and erase the computational benefit.
8. **Claiming strong convergence in every Hilbert space.** The basic variable-metric result gives weak convergence; extra regularity is needed for strong convergence.
9. **Claiming an objective rate from weak convergence.** A rate theorem needs a separate metric-aware potential and additional hypotheses.

Quasi-Newton forward–backward methods choose structured metrics, such as diagonal or low-rank modifications, to approximate curvature while preserving an efficient proximal calculation. Boundedness and positive definiteness still matter, and the proximal calculus must be proved for the chosen structure.

## 7. Exercises

1. Verify that the weighted inner product in (115.2) is positive definite.
2. Derive (115.4) from the first-order optimality condition of the metric proximal problem.
3. Prove the fixed-point equivalence (115.6), identifying exactly where invertibility of \(U\) is used.
4. Derive the weighted cocoercivity estimate (115.8) and the conservative step bound (115.9).
5. Show that \((1+\eta_k)U_{k+1}\succeq U_k\) implies (115.13) by reversing the Loewner order under inversion.
6. Verify that the sequence in (115.19) satisfies the metric variation condition and has a summable drift.
7. Compute the metric proximal map in (115.18) directly from its coordinatewise minimization problem.
8. Give an example where a dense metric makes a separable Euclidean proximal problem coupled.
9. Design a Lean structure for a self-adjoint strongly positive operator and list the lemmas needed before defining its weighted inner product.
10. Explain which extra invariant an accelerated variable-metric method would need beyond the quasi-Fejér estimate.

## 8. Chapter summary

Variable-metric forward–backward splitting replaces the scalar forward step with a positive operator and measures the proximal step in the corresponding inverse metric. A fixed metric changes the geometry but preserves the zero set. A varying metric requires uniform positivity, a uniform upper bound, and summable relative variation so the sequence of weighted distances remains quasi-Fejér.

In Lean, formalize operator order, weighted norms, the fixed-metric averaged map, and the variable-metric drift as separate layers. The transition certificate carries both the resolvent witness and the current geometry; the convergence proof consumes the summable variation only after the one-step estimate is established.

## Further reading

- Combettes and Vũ, [“Variable Metric Forward–Backward Splitting with Applications to Monotone Inclusions in Duality”](https://arxiv.org/abs/1206.6791), for the variable-metric convergence theorem and primal–dual applications.
- Becker, Fadili, and Ochs, [“On Quasi-Newton Forward-Backward Splitting: Proximal Calculus and Convergence”](https://doi.org/10.1137/18M1167152), for structured metrics and efficient metric proximal calculations.
- Chapters 94, 97, 113, and 114, for Bregman geometry, adaptive diagonal methods, fixed-metric forward–backward splitting, and backtracking.
