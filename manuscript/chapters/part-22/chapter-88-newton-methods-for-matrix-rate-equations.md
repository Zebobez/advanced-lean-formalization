# Chapter 88 — Newton Linearization for Matrix Rate Equations

> **Audience.** This chapter assumes familiarity with finite-dimensional derivatives, matrix-geometric rate equations, and the monotone iteration of Chapter 87. It derives the Newton correction for a noncommutative matrix polynomial and explains how to separate fast computation from proof of the desired root.

Monotone iteration is an excellent way to identify the least nonnegative rate matrix, but it can converge slowly near a critical regime. Newton methods use local linearization to accelerate the solution of the nonlinear equation. The difficulty is that a matrix equation has \(m^2\) unknown entries, multiplication is noncommutative, and a fast local solver may converge to the wrong root or leave the nonnegative cone.

This chapter derives the derivative as a linear map on matrices, turns the correction into a structured linear system, and explains what a Lean development must prove before accepting a computed answer. The key distinction is between solving the local equation quickly and certifying that the result is the least nonnegative rate matrix relevant to the queue.

## Learning objectives

After this chapter, you should be able to:

- differentiate a noncommutative matrix polynomial without changing factor order;
- derive the Newton correction for a finite-support rate equation;
- represent the correction as a linear operator or a Kronecker-product system;
- identify why a Newton step may leave the nonnegative cone;
- separate local convergence from global root selection and certification in Lean.

## 1. The residual equation

For finite downward-jump support, write the rate equation as

\[
R=F(R),\qquad F(X)=\sum_{j=0}^{d}X^jC_j,
\]

with nonnegative coefficient matrices \(C_j\). Define the residual map

\[
\Phi(X)=F(X)-X
=\sum_{j=0}^{d}X^jC_j-X.
\tag{88.1}
\]

The rate matrix is a zero of \(\Phi\). Newton's method starts from an approximation \(X\), linearizes the residual near \(X\), and chooses a correction \(H\) so that the linearized residual vanishes:

\[
\Phi(X)+D\Phi_X[H]=0.
\tag{88.2}
\]

After solving (88.2), the proposed next iterate is \(X+H\). This is a local root-finding step. It does not by itself prove that \(X+H\) is nonnegative, remains below any other fixed point, or is the least nonnegative solution.

## 2. Differentiate matrix powers in their given order

The derivative of \(X^j\) in direction \(H\) is

\[
D(X\mapsto X^j)_X[H]
=\sum_{i=0}^{j-1}X^iHX^{j-1-i}.
\tag{88.3}
\]

For \(j=2\), this is \(XH+HX\), not \(2XH\). The two expressions agree only when \(X\) and \(H\) commute, which is not a general assumption for matrices.

One proof expands the product \((X+tH)^j\). The terms linear in \(t\) are exactly those with one factor \(H\), placed in each of the \(j\) positions. Terms with two or more factors \(H\) contribute only to the remainder. Thus the derivative of (88.1) is

\[
D\Phi_X[H]
=\sum_{j=1}^{d}\sum_{i=0}^{j-1}
X^iHX^{j-1-i}C_j-H.
\tag{88.4}
\]

The \(j=0\) coefficient contributes no derivative because \(X^0C_0=C_0\) is constant. The final \(-H\) comes from differentiating \(-X\).

For every fixed \(X\), the map \(H\mapsto D\Phi_X[H]\) is linear. It is the Jacobian of the nonlinear residual, represented as a linear operator on the finite-dimensional vector space of \(m\times m\) matrices. Invertibility of this operator is the condition needed to solve the Newton correction uniquely.

## 3. The Newton correction equation

Substitute (88.4) into (88.2):

\[
\left(H-\sum_{j=1}^{d}\sum_{i=0}^{j-1}
X^iHX^{j-1-i}C_j\right)=\Phi(X).
\tag{88.5}
\]

Equivalently,

\[
(I-D F_X)[H]=F(X)-X.
\tag{88.6}
\]

Here \(I\) denotes the identity linear operator on matrices, not the identity matrix being multiplied on one side. This distinction is important: the operator \(H\mapsto H\) and the matrix \(I_m\) have different types even if both are written with an identity symbol.

If the linear operator in (88.5) is invertible, it determines \(H\). A Newton iteration then has the form

\[
X_{\mathrm{new}}=X+H.
\tag{88.7}
\]

The matrix equation for \(H\) is usually not solved by entrywise division. It is a coupled linear system involving all \(m^2\) entries. Depending on coefficient structure, it may be expressible as a Sylvester equation, a generalized Sylvester equation, or a Kronecker-product linear system.

### A quadratic rate equation

For

\[
F(X)=C_0+XC_1+X^2C_2,
\]

the derivative is

\[
DF_X[H]=HC_1+(XH+HX)C_2.
\tag{88.8}
\]

Thus the Newton correction solves

\[
H-HC_1-XHC_2-HXC_2
=C_0+XC_1+X^2C_2-X.
\tag{88.9}
\]

The three correction terms have different multiplication order. In particular, \(XHC_2\) and \(HXC_2\) are distinct linear functions of \(H\).

## 4. Vectorization and the Kronecker system

For a concrete finite computation, stack the entries of a matrix \(H\) into a vector \(\operatorname{vec}(H)\). The standard identity

\[
\operatorname{vec}(AHB)=(B^{\mathsf T}\otimes A)\operatorname{vec}(H)
\tag{88.10}
\]

turns a linear map on matrices into a square \(m^2\times m^2\) matrix. Applying it to (88.8) gives

\[
\operatorname{vec}(DF_X[H])
=\left(
C_1^{\mathsf T}\otimes I_m
+C_2^{\mathsf T}\otimes X
+(XC_2)^{\mathsf T}\otimes I_m
\right)\operatorname{vec}(H).
\tag{88.11}
\]

Therefore the correction can be computed by solving

\[
\left[
I_{m^2}
-C_1^{\mathsf T}\otimes I_m
-C_2^{\mathsf T}\otimes X
-(XC_2)^{\mathsf T}\otimes I_m
\right]\operatorname{vec}(H)
=\operatorname{vec}(\Phi(X)).
\tag{88.12}
\]

The transpose and factor order in (88.11) are determined by (88.10). A small vectorization lemma is worth proving once and reusing; it prevents a recurring class of silent transposition errors.

Vectorization is mathematically convenient but may be computationally expensive: the linear system has dimension \(m^2\), even when the original matrices are only \(m\times m\). A structured Sylvester solver can be more efficient. For formal verification, the full vectorized system can still serve as a simple specification against which a specialized solver is checked.

## 5. Worked example: Newton's method can leave the nonnegative cone

Return to the scalar equation

\[
\Phi(x)=0.1-0.8x+0.7x^2=0,
\]

whose nonnegative roots are \(1/7\) and \(1\). The derivative is \(\Phi'(x)=-0.8+1.4x\). Starting at \(x_0=0\), one Newton step gives

\[
x_1=0-\frac{0.1}{-0.8}=0.125.
\]

The next step gives

\[
\Phi(0.125)=0.0109375,\qquad
\Phi'(0.125)=-0.625,\qquad
x_2=0.125-\frac{0.0109375}{-0.625}=0.1425.
\]

These values approach the smaller root in this example. But a different starting point can fail: at \(x=0.5\), \(\Phi(0.5)=-0.125\) and \(\Phi'(0.5)=-0.1\), so Newton proposes

\[
x_{\mathrm{new}}=0.5-\frac{-0.125}{-0.1}=-0.75.
\]

The new point is negative even though the rate equation has positive solutions. A matrix Newton step can likewise leave the nonnegative cone, and no global monotonicity follows from the nonnegative coefficients of \(F\). This is why Chapter 87's order iteration remains valuable even when Newton steps are used to accelerate computation.

### 5.1 An executable Newton and noncommutative linearization certificate

The scalar example is exact over the rationals: the code verifies the two Newton steps from zero and the negative step produced from 1/2. It also checks the matrix square expansion and its quadratic remainder for arbitrary two-by-two rational matrices. A concrete pair of noncommuting matrices shows that the linear term (XH+HX) cannot be replaced by (2XH). These calculations verify the finite algebra in the Newton step; they do not prove a general Fréchet-derivative theorem or convergence.

```lean
def scalarResidual (x : ℚ) : ℚ := 1 / 10 - (4 / 5) * x + (7 / 10) * x ^ 2
def scalarResidualDerivative (x : ℚ) : ℚ := -(4 / 5) + (7 / 5) * x
def scalarNewtonStep (x : ℚ) : ℚ := x - scalarResidual x / scalarResidualDerivative x

theorem scalarResidual_factorization (x : ℚ) :
    scalarResidual x = ((7 * x - 1) * (x - 1)) / 10 := by
  unfold scalarResidual
  ring

theorem scalarNewton_first_step : scalarNewtonStep 0 = 1 / 8 := by
  norm_num [scalarNewtonStep, scalarResidual, scalarResidualDerivative]

theorem scalarNewton_second_step : scalarNewtonStep (1 / 8) = 57 / 400 := by
  norm_num [scalarNewtonStep, scalarResidual, scalarResidualDerivative]

theorem scalarNewton_bad_step : scalarNewtonStep (1 / 2) = -(3 / 4) := by
  norm_num [scalarNewtonStep, scalarResidual, scalarResidualDerivative]

abbrev NewtonMatrix := Matrix (Fin 2) (Fin 2) ℚ

def exampleX : NewtonMatrix := !![1, 1; 0, 1]
def exampleH : NewtonMatrix := !![0, 0; 1, 0]

theorem matrix_square_increment_expansion (X H : NewtonMatrix) :
    (X + H) ^ 2 = X ^ 2 + X * H + H * X + H ^ 2 := by
  simp only [pow_two, add_mul, mul_add]
  abel

theorem matrix_square_first_order_remainder (X H : NewtonMatrix) :
    (X + H) ^ 2 - X ^ 2 - (X * H + H * X) = H ^ 2 := by
  rw [matrix_square_increment_expansion]
  abel

theorem exampleXH_order_is_not_commutative :
    exampleX * exampleH ≠ exampleH * exampleX := by
  intro h
  have h11 := congrArg (fun M : NewtonMatrix => M 1 1) h
  norm_num [exampleX, exampleH, Matrix.mul_apply] at h11

theorem example_linearization_not_twice_left_product :
    exampleX * exampleH + exampleH * exampleX ≠ 2 • (exampleX * exampleH) := by
  intro h
  have h00 := congrArg (fun M : NewtonMatrix => M 0 0) h
  norm_num [exampleX, exampleH, Matrix.mul_apply] at h00
```

## 6. Local convergence, root selection, and safeguarding

For a smooth finite-dimensional residual, Newton's method converges quadratically when started sufficiently close to a simple root and when the Jacobian remains well behaved nearby. These are local hypotheses. A rate equation can have multiple roots, and the Newton basin depends on the starting point. The least nonnegative root is a global order-theoretic selection, not a consequence of local quadratic convergence.

There are several ways to keep computation and proof aligned:

1. Use monotone iteration from zero to obtain a certified lower bound.
2. Use a nonnegative supersolution to obtain an upper bound for the least fixed point.
3. Let Newton or Newton–Shamanskii propose a faster candidate inside that bracket.
4. Verify a residual enclosure and a local inverse/Jacobian bound, or continue the monotone bracket until it is sufficiently narrow.

A damping factor \(\alpha\in(0,1]\) replaces \(H\) by \(\alpha H\), but damping alone is not a theorem. A line search must verify the property it is intended to preserve, such as nonnegativity, a decrease in a chosen residual norm, or membership in a region where a convergence theorem applies.

The Newton–Shamanskii method reuses a Jacobian or related linearization for several updates to reduce computational cost. Its convergence and monotonicity require hypotheses beyond the derivative formula. In a formal library, keep the following statements separate:

- a theorem that (88.4) is the derivative of the residual;
- a theorem that the correction solves the linearized equation;
- a convergence theorem under local or order-theoretic assumptions;
- a root-selection theorem showing the limit is the least nonnegative solution.

This layering allows a verified derivative to support several algorithms without claiming that every algorithm has the same convergence behavior.

### A local quadratic error estimate

Let \(R\) be a root, let \(J(X)=D\Phi_X\), and suppose the Jacobian is invertible near \(R\). Assume it is Lipschitz on a convex neighborhood:

\[
\|J(X)-J(Y)\|\leq L\|X-Y\|,
\qquad
\|J(X)^{-1}\|\leq M_J.
\tag{88.13}
\]

Taylor's theorem with a Lipschitz derivative bounds the linearization remainder by \(L\|R-X\|^2/2\). The Newton correction cancels the linear part, giving

\[
\|X_{\mathrm{new}}-R\|
\leq \frac{M_JL}{2}\|X-R\|^2.
\tag{88.14}
\]

For the polynomial map on a norm-bounded region \(\|X\|\leq M\), a usable, though sometimes conservative, Lipschitz constant for its derivative is

\[
L\leq\sum_{j=2}^{d}j(j-1)M^{j-2}\|C_j\|.
\tag{88.15}
\]

This explains quadratic convergence near a simple, well-conditioned root. It does not determine which root the method reaches: the estimate applies around whichever root \(R\) satisfies the hypotheses.

The factor \(M_J\) measures local conditioning. If the Jacobian is nearly singular, a small residual can correspond to a much larger error in the matrix. A proof should therefore report the inverse-Jacobian bound alongside the residual, rather than using residual size as a proxy for accuracy. A rate matrix near a stability boundary may be numerically delicate, but \(\rho(R)\) near one alone does not prove that the Jacobian is singular; the two conditions must be analyzed separately.

### Sensitivity of the full rate matrix

The same Jacobian gives first-order parameter sensitivity. Suppose the coefficients depend differentiably on \(\theta\), and a differentiable root branch satisfies \(\Phi(R(\theta),\theta)=0\). Differentiating this identity yields

\[
J(R,\theta)[R'(\theta)]
=-\partial_\theta\Phi(R,\theta).
\tag{88.16}
\]

For \(\Phi(X,\theta)=\sum_jX^jC_j(\theta)-X\), the right-hand side is \(-\sum_jR^jC'_j(\theta)\). If \(J(R,\theta)\) is invertible, the derivative is obtained by solving the same type of structured linear system used for a Newton correction. This is the matrix analogue of implicit differentiation and complements the Perron-root sensitivity formula in Chapter 86. It is a local statement about a chosen root branch; it does not establish that a different branch remains least under all parameter changes.

## 7. Lean proof architecture

### 7.1 Treat matrices as a finite-dimensional normed space

For a finite phase type, \(m\times m\) real matrices form a finite-dimensional real vector space. Define \(\Phi\) as a finite sum of polynomial maps. There are two proof routes:

- use the Fréchet derivative API for finite-dimensional normed spaces and prove the derivative formula (88.4);
- establish the formula by a direct expansion of \((X+H)^j\), grouping terms by the number of \(H\) factors.

The API route gives a reusable differentiability theorem. The expansion route makes multiplication order visible and may be easier for a first proof. In either case, prove the power derivative (88.3) independently, then compose with right multiplication by \(C_j\) and sum over coefficients.

### 7.2 Represent the Jacobian as a linear map

The safest abstract representation is a linear map from the matrix space to itself. Define the residual as the polynomial minus the identity function, and define its Jacobian at \(X\) by the right-hand side of (88.4). A derivative theorem then states that this linear map is the Fréchet derivative of the residual at \(X\). A correction theorem can assume that the Jacobian is bijective, then use the inverse linear map to define the unique \(H\) solving the linearized residual equation. This avoids prematurely choosing a concrete vectorization order.

For executable computation, define an explicit equivalence between matrices and vectors indexed by pairs of phases, then prove the Kronecker identity (88.10). The abstract linear-map interface and the concrete vectorized solver should be connected by one equivalence theorem.

A numerical inverse for the Jacobian can also be certified. If a proposed inverse \(B\) satisfies \(\|I-BJ(X)\|<1\), the Neumann-series theorem makes \(BJ(X)\) invertible. In finite dimensions this implies that \(J(X)\) is bijective; the same estimate bounds the inverse norm. This turns an approximate linear algebra computation into hypotheses for the local error estimate, provided all norms and interval bounds are verified.

### 7.3 Verify candidates independently of the solver

An external numerical solver can return \(X\) and \(H\). A proof assistant need only check:

- the residual value \(\Phi(X)\) or a certified enclosure of it;
- the Jacobian action \(D\Phi_X[H]\);
- the correction equation (88.2);
- nonnegativity or interval bounds required by the outer certificate.

This turns the numerical solver into an untrusted proposal generator. The proof is carried by the verified equations and enclosures. A small residual is not enough on its own; it must be paired with an inverse bound, contraction theorem, or monotone lower/upper certificate.

### 7.4 Preserve noncommutative algebra in simplification

Do not ask a commutative ring normalizer to rearrange matrix products. State and use identities such as

\[
(X+H)^2=X^2+XH+HX+H^2
\]

with each product in its original order. For general powers, prove the first-order decomposition by induction and isolate the remainder terms containing at least two copies of \(H\). This yields both the derivative formula and explicit norm bounds for local convergence proofs.

## 8. Common failure modes

1. **Replacing \(XH+HX\) by \(2XH\).** This assumes commutativity that arbitrary matrices do not satisfy.
2. **Differentiating only the leftmost occurrence.** Every position in \(X^j\) contributes a first-order term.
3. **Dropping the constant term from the residual incorrectly.** \(C_0\) contributes to \(\Phi(X)\), even though it contributes nothing to the derivative.
4. **Using the matrix identity as the Jacobian identity.** The Jacobian is a linear operator on perturbation matrices.
5. **Ignoring vectorization transposes.** Formula (88.10) fixes the Kronecker-factor order.
6. **Assuming a small residual proves a nearby root.** A conditioning or contraction bound is also required.
7. **Assuming Newton preserves nonnegativity.** The scalar example at \(x=0.5\) already disproves that general claim.
8. **Confusing local convergence with leastness.** A fast-converging root may not be the minimal nonnegative rate matrix.
9. **Treating damping as a convergence proof.** The chosen step still needs a verified invariant region or theorem.
10. **Proving one algorithm's behavior from another's theorem.** Newton, Newton–Shamanskii, and monotone functional iteration have distinct hypotheses.

## 9. Exercises

1. Prove (88.3) by induction using the expansion of \((X+H)^j\) to first order in \(H\).
2. Derive (88.4) from the residual (88.1), explicitly accounting for the \(j=0\) term.
3. Derive the quadratic correction equation (88.9).
4. Prove the vectorization identity (88.10) from the definition of the Kronecker product and column-stacking convention.
5. Recompute the Kronecker coefficient for \(HXC_2\) and explain why it differs from the coefficient for \(XHC_2\).
6. Verify both Newton steps in the scalar example and factor \(\Phi(x)\) to identify its two roots.
7. Give a nonnegative initial matrix and nonnegative polynomial coefficients for which a Newton step has a negative entry.
8. State sufficient hypotheses for local quadratic convergence of Newton's method in a finite-dimensional normed space.
9. Design an interface separating the derivative theorem, correction solver, local convergence theorem, and least-root certificate.
10. Explain how Chapter 87's monotone lower and upper bounds can certify a root proposed by Newton iteration.

## 10. Summary

The finite-support rate equation is a matrix polynomial root problem. Its derivative is a linear operator on perturbation matrices, with one term for each position in each matrix power. Newton's correction solves a structured linear system; vectorization turns that system into a Kronecker matrix equation.

The derivative and correction equations are algebraic and reusable. Global convergence, preservation of nonnegativity, and selection of the least nonnegative rate matrix require additional hypotheses. A dependable formalization proves the local linearization once, then combines accelerated candidate generation with monotone or residual-based certificates.

### Further reading

- M. F. Neuts, [“Markov chains with applications in queueing theory, which have a matrix-geometric invariant probability vector”](https://doi.org/10.2307/1426725), *Advances in Applied Probability* 10 (1978), 185–212. This paper establishes the minimal nonnegative rate-matrix framework.
- J. Pérez and B. Van Houdt, [“A fast Newton–Shamanskii iteration for M/G/1-type and GI/M/1-type Markov chains”](https://arxiv.org/abs/1508.06341), 2015. This work studies Newton-like acceleration and convergence for the matrix equations arising in these chains.
