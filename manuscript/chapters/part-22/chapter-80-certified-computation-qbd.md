# Chapter 80 — Certified Computation for Matrix-Geometric Tails

> **Audience.** This chapter builds on the QBD balance equations and rate matrix from Chapter 79. It assumes familiarity with finite-dimensional normed spaces, matrix multiplication, and numerical approximation. The focus is how to turn a computed matrix into a mathematical certificate that can be checked independently of the algorithm that produced it.

Many useful mathematical objects are not pleasant to express in closed form. The QBD rate matrix is a typical example: it is the minimal nonnegative solution of a nonlinear matrix equation, and practical models usually require numerical computation. A floating-point approximation is useful for exploration, but its small residual alone does not establish that an exact solution is nearby.

This chapter develops a proof-oriented alternative. First, rewrite the rate-matrix equation as a fixed-point problem. Then place the fixed-point map inside a closed region where it is a contraction. The contraction gives existence, uniqueness, and an explicit error bound. Finally, propagate the matrix bound into a certified bound on the stationary tail. The same structure separates naturally into computational and proof layers in Lean.

## Learning objectives

After this chapter, you should be able to:

- rewrite the QBD rate-matrix equation as a monotone fixed-point equation;
- use a contraction region to prove that an approximation is close to the exact rate matrix;
- explain why a small residual is not by itself an error estimate;
- bound probability mass above a chosen level using a matrix norm;
- design a Lean certificate that separates approximate computation from exact verification.

## 1. From an equation to a checkable certificate

Chapter 79 derived the continuous-time QBD equation

\[
A_1+RA_0+R^2A_{-1}=0.
\tag{80.1}
\]

The equation is finite-dimensional, but it is nonlinear and its matrix factors do not commute. A numerical solver may return an approximate matrix \(\widetilde R\), but what mathematical statement should we prove about it?

A useful certificate has four layers:

1. an exact description of the input blocks;
2. a region that contains the exact solution;
3. an error bound for the computed approximation;
4. a bound on the stationary quantities that depend on that solution.

The solver itself need not be trusted. It can be a floating-point routine, a symbolic system, or a custom Lean program. The final checker only needs to verify the certificate.

~~~text
exact QBD blocks
       |
       v
fixed-point map and invariant region
       |
       v
computed approximation + contraction bound
       |
       v
enclosure of the rate matrix R
       |
       v
certified stationary tail and truncation error
~~~

This flow is particularly useful when the output will support a quantitative claim such as “the probability of a queue length above level \(N\) is less than \(\varepsilon\).”

## 2. Deriving a fixed-point map

Set

\[
M=-A_0.
\]

Assume \(M\) is invertible and its inverse is entrywise nonnegative. In common QBD models, \(-A_0\) is a nonsingular M-matrix; this can be established from the within-level rates and transience of the within-level subgenerator. For this derivation, keep invertibility and inverse nonnegativity as explicit hypotheses rather than silently assuming them.

Equation (80.1) becomes

\[
A_1-RM+R^2A_{-1}=0.
\]

Right-multiply by \(M^{-1}\):

\[
R=(A_1+R^2A_{-1})M^{-1}.
\tag{80.2}
\]

Define the map

\[
F(X)=(A_1+X^2A_{-1})M^{-1}.
\tag{80.3}
\]

Every fixed point of \(F\) solves the QBD quadratic, and every solution of that quadratic is a fixed point, provided \(M\) is invertible. If \(A_1\), \(A_{-1}\), and \(M^{-1}\) are entrywise nonnegative, then \(F\) maps entrywise nonnegative matrices to entrywise nonnegative matrices.

The map is also monotone on that cone. If \(0\leq X\leq Y\) entrywise, multiplication by nonnegative matrices preserves order. In particular,

\[
X^2\leq XY\leq Y^2,
\]

so \(F(X)\leq F(Y)\). This monotonicity makes iteration from zero useful:

\[
X_0=0,\qquad X_{k+1}=F(X_k).
\tag{80.4}
\]

The sequence is increasing because \(X_0\leq X_1\), and monotonicity then gives \(X_k\leq X_{k+1}\) at each step. If the iterates are bounded above by a nonnegative solution, they converge entrywise in finite dimensions. Continuity of \(F\) makes the limit a fixed point. Since every nonnegative fixed point bounds the iterates from above, this limit is the least nonnegative fixed point.

This gives an elementary route to minimality for the iteration when its assumptions hold. A separate numerical method may be much faster, but it can still be checked against the same equation and order properties.

## 3. A contraction certificate

Monotone convergence tells us which solution an iteration approaches, but it does not by itself say how fast. For a quantitative error estimate, choose a submultiplicative matrix norm and a radius \(r>0\). Let

\[
\mathcal C=\{X: X\geq0\text{ entrywise and }\|X\|\leq r\}.
\]

This is a closed subset of a finite-dimensional normed space, so it is complete. Define

\[
u=\|A_1M^{-1}\|,\qquad
c=\|A_{-1}M^{-1}\|.
\]

For \(X\in\mathcal C\),

\[
\|F(X)\|
\leq \|A_1M^{-1}\|+\|X^2A_{-1}M^{-1}\|
\leq u+r^2c.
\]

Thus \(\mathcal C\) is invariant under \(F\) if

\[
u+r^2c\leq r.
\tag{80.5}
\]

For \(X,Y\in\mathcal C\), use the noncommutative factorization

\[
X^2-Y^2=X(X-Y)+(X-Y)Y.
\]

Then

\[
\begin{aligned}
\|F(X)-F(Y)\|
&=\|(X^2-Y^2)A_{-1}M^{-1}\|\\
&\leq (\|X\|+\|Y\|)\,c\,\|X-Y\|\\
&\leq 2rc\,\|X-Y\|.
\end{aligned}
\]

Therefore \(F\) is a contraction on \(\mathcal C\) when

\[
q=2rc<1.
\tag{80.6}
\]

Under (80.5) and (80.6), the contraction theorem gives a unique fixed point in \(\mathcal C\). Starting from any point in the region and iterating \(F\) converges to that fixed point. Starting from zero also retains the monotone approximation from the previous section.

These inequalities are sufficient conditions, not necessary conditions for a QBD to be stable. The chosen norm may be too coarse to prove them even when the queue is positive recurrent. A failed contraction estimate says that this particular certificate is insufficient; it does not prove that the underlying QBD has no stationary law.

## 4. Turning an iterate into an error bound

Let \(R\) be the fixed point in \(\mathcal C\), and let \(X_k\) be an iterate. If \(q<1\), the contraction estimate gives the a priori bound

\[
\|X_k-R\|
\leq \frac{q^k}{1-q}\|X_1-X_0\|.
\tag{80.7}
\]

Often an a posteriori bound is more useful, because it uses the observed difference between the last two iterates. Let

\[
d_k=\|X_k-X_{k-1}\|.
\]

All later differences are bounded by \(qd_k,q^2d_k,\ldots\). Summing the geometric series yields

\[
\|X_k-R\|
\leq \frac{q}{1-q}d_k.
\tag{80.8}
\]

There is also a residual form. For any \(X\in\mathcal C\),

\[
\begin{aligned}
\|X-R\|
&\leq \|X-F(X)\|+\|F(X)-F(R)\|\\
&\leq \|X-F(X)\|+q\|X-R\|.
\end{aligned}
\]

Rearranging gives

\[
\|X-R\|\leq \frac{\|X-F(X)\|}{1-q}.
\tag{80.9}
\]

Equation (80.9) explains when a residual is useful: it becomes an error estimate only together with a stability bound such as the contraction constant. The residual and contraction factor should both be part of the certificate.

## 5. Worked example: a certified scalar rate

Take an M/M/1 queue with arrival rate \(\lambda=2/3\) and service rate \(\mu=1\). Chapter 79 gives \(A_1=2/3\), \(A_0=-5/3\), and \(A_{-1}=1\). Thus \(M=5/3\), and (80.3) becomes

\[
F(x)=\frac{2+3x^2}{5}.
\]

Choose the interval \(\mathcal C=[0,3/4]\). Since \(F\) is increasing there, its image is bounded by its endpoint values:

\[
F(0)=\frac25,\qquad F(3/4)=\frac{59}{80}<\frac34.
\]

Hence \(F(\mathcal C)\subseteq\mathcal C\). Its derivative is \(F'(x)=6x/5\), so for \(x\in\mathcal C\),

\[
|F'(x)|\leq\frac{9}{10}<1.
\]

The map is a contraction with \(q=9/10\). Its fixed points solve

\[
3x^2-5x+2=0,
\]

whose roots are \(2/3\) and \(1\). Only \(2/3\) lies in \(\mathcal C\), so the unique fixed point in the certified interval is \(R=2/3\).

Starting with \(x_0=0\), the first iterate is \(x_1=2/5\). The a priori estimate is

\[
|x_k-R|\leq 4(9/10)^k.
\]

This bound is valid but conservative. If a later exact computation gives, for instance, \(|x_k-x_{k-1}|\leq 10^{-8}\), the a posteriori estimate (80.8) gives

\[
|x_k-R|\leq \frac{9/10}{1/10}\,10^{-8}=9\cdot10^{-8}.
\]

The numerical value need not be guessed from a plot or trusted from a floating-point solver. A checker verifies interval invariance, the contraction constant, and the exact rational iterate difference.

## 6. Worked example: converting a matrix bound into a tail bound

Suppose a two-phase QBD has a certified rate matrix with entrywise nonnegative entries and induced matrix 1-norm

\[
\|R\|_1\leq 0.7.
\]

Suppose the level-one stationary vector satisfies \(\|\pi_1\|_1\leq0.2\). For a nonnegative row vector, its 1-norm is its total mass. Therefore the probability of being above level \(N\) is

\[
\begin{aligned}
\mathbb P(L>N)
&=\sum_{n=N+1}^{\infty}\pi_1R^{n-1}\mathbf 1\\
&\leq\sum_{k=N}^{\infty}\|\pi_1R^k\|_1\\
&\leq\|\pi_1\|_1\sum_{k=N}^{\infty}\|R\|_1^k\\
&\leq 0.2\,\frac{0.7^N}{1-0.7}.
\end{aligned}
\tag{80.10}
\]

For \(N=20\), the upper bound is less than \(5.32\times10^{-4}\). This is a certified truncation error: a finite computation retaining levels zero through twenty omits less than this amount of stationary probability, assuming the stated norm bounds have themselves been verified.

The same estimate guides adaptive computation. If a desired tail tolerance is \(\varepsilon\), choose \(N\) so that

\[
\|\pi_1\|_1\frac{r^N}{1-r}\leq\varepsilon
\]

for a proved bound \(\|R\|_1\leq r<1\). The estimate is conservative, but it is transparent and inexpensive to verify. Tighter phase-sensitive bounds can be developed later if this estimate is too large.

## 7. Why a small residual is not enough

For a proposed approximation \(\widetilde R\), the quadratic residual is

\[
P(\widetilde R)=A_1+\widetilde R A_0+\widetilde R^2A_{-1}.
\]

A small value of \(\|P(\widetilde R)\|\) shows that \(\widetilde R\) nearly satisfies the equation. It does not, by itself, bound the distance to an exact solution. In the scalar equation \(f(x)=\delta(x-a)\), an approximation \(x=a+\eta\) has residual \(|\delta\eta|\). For small \(\delta\), the residual can be tiny while the error \(|\eta|\) is large.

The same issue appears for matrix equations through a poorly conditioned derivative or nearly multiple roots. A robust proof therefore combines the residual with a local inverse estimate, a verified Newton-type argument, or a contraction region. This chapter uses a contraction because its inequalities are elementary and its Lean interface is reusable.

There is another practical distinction between floating-point and exact certificates. A displayed decimal such as \(0.7000001\) is not automatically an upper bound. One needs either an interval enclosure whose endpoints are represented exactly, or a rational upper bound proved to dominate the computed value. Directed rounding and outward error control belong in the certificate, not in an informal comment about the solver.

## 8. Formalizing the certificate in Lean

The finite phase type makes the matrices finite-dimensional. Keep the analytic argument independent from the algorithm that proposes the approximation. A useful certificate record can contain:

- the QBD blocks and proofs of the generator sign and row-sum conditions;
- invertibility of \(M=-A_0\) and entrywise nonnegativity of \(M^{-1}\);
- nonnegativity of \(A_1\) and \(A_{-1}\);
- a radius \(r\), the invariant-region inequality (80.5), and a contraction bound \(q<1\);
- an approximation \(X\) and a proved upper bound on \(\|X-F(X)\|\) or \(\|X_k-X_{k-1}\|\);
- a bound \(\|\pi_1\|_1\leq c_0\) if a stationary tail estimate is desired.

Then divide the formal development into small theorems:

1. **Algebraic equivalence.** Under \(M\) invertible, prove that \(F(R)=R\) is equivalent to (80.1). This proof is a short matrix rearrangement; preserve multiplication order.
2. **Positivity and monotonicity.** Show that \(F\) maps the nonnegative cone to itself and is monotone there. These lemmas use finite sums of nonnegative products.
3. **Invariant region.** Prove (80.5) implies that \(F(X)\in\mathcal C\) whenever \(X\in\mathcal C\).
4. **Contraction.** Prove the factorization of \(X^2-Y^2\) and apply submultiplicativity to obtain \(q=2rc\).
5. **Error and tail bounds.** Derive (80.8)–(80.10) from the contraction and norm inequalities.

The checker can use exact rational data for small examples. For larger models, interval arithmetic can produce rational interval endpoints; Lean then verifies the endpoint inequalities and the algebraic relations. The trusted proof should consume the enclosure, not the undocumented internal state of an external numerical program.

Matrix order is a particularly important formalization detail. The identity \(X^2-Y^2=X(X-Y)+(X-Y)Y\) is valid without commutativity. Replacing it by \((X+Y)(X-Y)\) would silently assume \(XY=YX\), which generally fails. An explicit Lean calculation chain or a named factorization lemma makes the correct order visible.

If a development uses real-valued matrices, exact rational bounds can still certify real inequalities by coercion. It is often easier to compute the candidate entries as rationals, prove a rational interval contains the exact real solution, then use that interval in the probability estimate. Avoid turning every numerical operation into a proof by reflection before the mathematical certificate has been designed.

## 9. Choosing a numerical method

The monotone fixed-point iteration is a good first method because the mathematical invariant is easy to state: iterates are nonnegative, increasing, and bounded by a solution. Under a contraction certificate, it also gives a direct error estimate. Its weakness is speed; a contraction factor close to one can make many iterations necessary.

Specialized QBD algorithms, including logarithmic reduction and doubling methods, exploit the repeated block structure to improve numerical performance. Their derivations and recurrence equations are more involved, but the final output can still be checked with a simpler certificate: nonnegativity, a small verified residual, a contraction or enclosure argument, and the QBD boundary and normalization equations. The numerical method may be sophisticated while the proof checker remains small.

For a large model, separate three goals:

- **Compute:** obtain a high-quality approximation quickly.
- **Enclose:** prove that an exact rate matrix lies in a specified region.
- **Use:** propagate that enclosure to stationary probabilities or a tail tolerance.

A single algorithm does not need to optimize all three. This separation also helps diagnose failure. If iteration is slow, change the solver. If the enclosure is too wide, improve the norm or interval bounds. If the tail estimate is loose, refine the phase-sensitive estimate without changing the root-finding proof.

## 10. Common failure modes

1. **Inverting the wrong block side.** Equation (80.2) uses a right multiplication by \(M^{-1}\). Reordering factors changes the map.
2. **Assuming the inverse is nonnegative.** Invertibility alone does not imply that \(M^{-1}\) preserves the nonnegative cone.
3. **Using a contraction constant without an invariant region.** A Lipschitz estimate near a candidate does not prove that iteration stays in the region.
4. **Treating a residual as an error bound.** A residual needs conditioning information, such as the contraction factor in (80.9).
5. **Using rounded decimals as inequalities.** Store outward-rounded or rational bounds and prove the comparisons.
6. **Proving convergence but not identifying the branch.** The monotone iteration from zero or uniqueness in a verified region connects the limit to the intended nonnegative solution.
7. **Applying a matrix norm bound to probabilities without positivity.** The tail estimate uses nonnegative level masses so their sum is controlled by the vector 1-norm.
8. **Confusing a finite truncation with an infinite model.** A truncation is justified only after the omitted tail is bounded or a convergence result is proved.

## 11. Exercises

1. **Derive the fixed-point map.** Starting from (80.1), set \(M=-A_0\), assume \(M\) is invertible, and derive (80.2). Identify every right multiplication used.
2. **Prove monotonicity.** If \(0\leq X\leq Y\), show \(X^2\leq Y^2\) entrywise and conclude \(F(X)\leq F(Y)\) under the stated block assumptions.
3. **Check an invariant interval.** For the scalar map \(F(x)=(2+3x^2)/5\), verify that \([0,3/4]\) is invariant and find a valid contraction constant.
4. **A posteriori error.** Suppose a contraction factor is at most \(1/5\), and the last two iterates differ by at most \(3\times10^{-9}\). Bound the distance from the newest iterate to the fixed point.
5. **Tail budget.** With \(\|\pi_1\|_1\leq0.12\) and \(\|R\|_1\leq0.6\), find a level \(N\) that makes the bound in (80.10) smaller than \(10^{-5}\).
6. **Residual counterexample.** For \(f(x)=\delta(x-a)\), choose \(\delta\) and an approximation error \(\eta\) so that the residual is below \(10^{-6}\) while the error exceeds \(10^{-2}\).
7. **Lean interface.** List which certificate fields are necessary for algebraic equivalence, which are needed for fixed-point error, and which are needed for the stationary tail estimate.
8. **Method comparison.** Explain why a fast doubling algorithm can be paired with a simple exact checker. State which facts the checker must establish even if it never repeats the doubling computation.

## 12. Summary

The QBD rate-matrix quadratic can be rewritten as the fixed-point equation

\[
R=(A_1+R^2A_{-1})(-A_0)^{-1},
\]

when the inverse exists. Monotone iteration from zero identifies the least nonnegative fixed point under the stated positivity and boundedness assumptions. A closed invariant region and a contraction constant give quantitative error bounds for an approximate matrix. A norm bound below one then converts the matrix enclosure into an explicit stationary-tail estimate.

The formalization should distinguish computation from verification. The solver proposes an answer; the proof checks the invariant region, contraction or residual bound, QBD equations, and tail estimate. This approach makes numerical output reproducible, auditable, and useful in a formal proof.

### Further reading

- G. Latouche and V. Ramaswami, *Introduction to Matrix Analytic Methods in Stochastic Modeling*, ASA-SIAM Series on Statistics and Applied Probability, 1999, Chapter 8, [“Algorithms for the Rate Matrix”](https://doi.org/10.1137/1.9780898719734.ch8). This chapter surveys iterative equations and numerical methods for QBD rate matrices.
- G. Latouche and V. Ramaswami, “A logarithmic reduction algorithm for quasi-birth-death processes,” *Journal of Applied Probability* 30 (1993), 650–674, [doi:10.1017/S0021900200044387](https://doi.org/10.1017/S0021900200044387). This is a foundational structure-exploiting algorithm for the QBD setting.
- G. Hanukov and U. Yechiali, “Explicit solutions for continuous-time QBD processes by using relations between matrix geometric analysis and the probability generating functions method,” *Probability in the Engineering and Informational Sciences* 35 (2021), 565–580, [doi:10.1017/S0269964819000470](https://doi.org/10.1017/S0269964819000470). This paper relates matrix-geometric computation to generating functions and the rate-matrix equation.
