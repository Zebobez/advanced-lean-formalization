# Chapter 87 — Monotone Construction of the Rate Matrix

> **Audience.** This chapter assumes familiarity with matrix-geometric stationary laws, entrywise order on matrices, and finite-dimensional limits. It studies a constructive proof that iteration from zero finds the least nonnegative solution of a finite-support GI/M/1-type rate equation.

The rate matrix in Chapter 84 is defined by a nonlinear equation. A numerical method may approximate a solution, but a formal development needs to know which solution it is approximating and why. For finitely many possible downward jumps, the rate equation is a matrix polynomial with nonnegative coefficients. Its order structure gives a particularly transparent construction: start at zero and repeatedly apply the polynomial map.

This chapter proves that the iterates increase to the least nonnegative fixed point whenever any nonnegative fixed point exists. It then develops lower and upper certificates, a conditional contraction error bound, and proof interfaces suitable for Lean. The argument is elementary but powerful: it replaces an opaque root-selection claim with an explicit sequence and a leastness theorem.

## Learning objectives

After this chapter, you should be able to:

- write the finite-support GI/M/1 rate equation as a monotone polynomial map;
- prove that iteration from zero converges to its least nonnegative fixed point;
- use supersolutions to certify upper bounds for the rate matrix;
- turn a contraction estimate into a rigorous residual error bound;
- separate the algebraic fixed point from stability and stationary normalization;
- structure the monotone-limit proof using finite matrix entries in Lean.

## 1. A finite-support rate equation

Use the increment convention from Chapter 84. Suppose positive-level downward jumps are bounded, so there is some \(d\in\mathbb N\) such that \(A_{1-j}=0\) for all \(j>d\). The rate equation (84.8) becomes the finite polynomial equation

\[
R=\sum_{j=0}^{d}R^jC_j,
\qquad C_j:=A_{1-j}.
\tag{87.1}
\]

Every coefficient matrix \(C_j\) is entrywise nonnegative. Define the map

\[
F(X)=\sum_{j=0}^{d}X^jC_j
\tag{87.2}
\]

on nonnegative square matrices of the phase dimension. Then (87.1) says exactly that \(R\) is a fixed point of \(F\).

For matrices, write \(X\leq Y\) when every entry of \(X\) is at most the corresponding entry of \(Y\). This is a partial order, not an order compatible with arbitrary multiplication. The nonnegativity hypotheses are essential: if \(X,Y,C\) are nonnegative and \(X\leq Y\), then products preserve the relevant inequalities, but this can fail when entries have mixed signs.

### Monotonicity of the polynomial map

Assume \(0\leq X\leq Y\). For each integer \(j\geq1\), the noncommutative identity

\[
Y^j-X^j
=\sum_{i=0}^{j-1}Y^i(Y-X)X^{j-1-i}
\tag{87.3}
\]

expresses the power difference as a sum of nonnegative matrix products. Therefore \(X^j\leq Y^j\). Right multiplication by \(C_j\geq0\) preserves this order, and summing the terms gives

\[
F(X)\leq F(Y).
\tag{87.4}
\]

The order argument uses the displayed factor order. A scalar proof that silently commutes \(X\), \(Y\), or \(C_j\) would not establish (87.4) for matrices.

## 2. Iteration from zero gives the least fixed point

Define a sequence of matrices by

\[
X_0=0,\qquad X_{n+1}=F(X_n).
\tag{87.5}
\]

The initial step is \(X_0\leq X_1\), since \(X_1=C_0\geq0\). If \(X_n\leq X_{n+1}\), monotonicity of \(F\) gives

\[
X_{n+1}=F(X_n)\leq F(X_{n+1})=X_{n+2}.
\]

Thus the sequence is increasing entrywise.

Now suppose \(S\geq0\) is any fixed point of \(F\). Since \(X_0=0\leq S\), induction and monotonicity show

\[
X_n\leq S\qquad\text{for every }n.
\tag{87.6}
\]

In particular, if at least one nonnegative fixed point exists, the increasing sequence is bounded above entrywise. Each entry is an increasing bounded sequence of real numbers, so it converges. Let \(X_\infty\) be the matrix of entrywise limits. The map \(F\) is a finite polynomial and hence continuous, so

\[
F(X_\infty)
=F\!\left(\lim_{n\to\infty}X_n\right)
=\lim_{n\to\infty}F(X_n)
=\lim_{n\to\infty}X_{n+1}
=X_\infty.
\tag{87.7}
\]

The limit is a fixed point. Applying (87.6) to any nonnegative fixed point \(S\) and passing to the limit gives \(X_\infty\leq S\). Therefore \(X_\infty\) is the least nonnegative fixed point.

This theorem has a useful existence boundary. We have not assumed a queue is stable; we assumed only that a nonnegative fixed point exists. The iteration constructs the least algebraic solution. To use it as a stationary rate matrix, one still needs the conditions from matrix-analytic theory: in particular, the relevant solution must have spectral radius below one, and the boundary balance and normalization equations must produce a stationary probability law.

## 3. Worked example: scalar iteration and a certified bracket

For the scalar rate equation from Chapter 84,

\[
r=0.1+0.2r+0.7r^2,
\tag{87.8}
\]

the fixed-point map is \(F(x)=0.1+0.2x+0.7x^2\). Starting at \(x_0=0\) gives

\[
x_1=0.1,\qquad
x_2=0.127,\qquad
x_3=0.1366903.
\tag{87.9}
\]

The map is increasing on \([0,\infty)\), and these iterates increase toward the smaller root \(1/7\). The other root is \(1\). Iteration from zero identifies the least nonnegative root without asking a polynomial solver to choose between them.

The iteration also gives lower bounds. A rational supersolution supplies an upper bound. For \(\bar x=0.15\),

\[
F(\bar x)=0.1+0.2(0.15)+0.7(0.15)^2=0.14575\leq0.15.
\tag{87.10}
\]

Since \(x_0\leq\bar x\), monotonicity proves \(x_n\leq\bar x\) for every \(n\). The least fixed point lies between the current iterate and this supersolution:

\[
x_n\leq r_{\min}\leq0.15.
\tag{87.11}
\]

Both endpoints can be rational, so a proof assistant can check the enclosure by exact arithmetic. A tighter supersolution or more iterations narrows the interval. This is a simple prototype of a proof-carrying numerical result: the computational procedure proposes a matrix, while the formal theorem verifies the inequalities that certify it.

## 4. Worked example: preserving order with noncommuting matrices

Consider a two-phase polynomial map

\[
F(X)=C_0+XC_1+X^2C_2,
\]

where

\[
C_0=\begin{pmatrix}0.05&0\\0&0.04\end{pmatrix},\quad
C_1=\begin{pmatrix}0.1&0.05\\0.02&0.1\end{pmatrix},\quad
C_2=\begin{pmatrix}0.2&0\\0&0.15\end{pmatrix}.
\tag{87.12}
\]

Take

\[
X=\begin{pmatrix}0.1&0\\0&0.1\end{pmatrix},
\qquad
Y=\begin{pmatrix}0.2&0.1\\0&0.2\end{pmatrix}.
\tag{87.13}
\]

Then \(0\leq X\leq Y\). For the linear term,

\[
YC_1-XC_1=(Y-X)C_1
=\begin{pmatrix}0.012&0.015\\0.002&0.01\end{pmatrix}\geq0.
\]

For the quadratic term, use (87.3):

\[
Y^2-X^2=(Y-X)Y+X(Y-X)
=\begin{pmatrix}0.03&0.04\\0&0.03\end{pmatrix}.
\]

Thus

\[
(Y^2-X^2)C_2
=\begin{pmatrix}0.006&0.006\\0&0.0045\end{pmatrix}\geq0,
\]

and adding the two differences gives

\[
F(Y)-F(X)
=\begin{pmatrix}0.018&0.021\\0.002&0.0145\end{pmatrix}\geq0.
\]

The example is an order calculation, not a complete queue model. It makes the proof obligation concrete: matrix multiplication order is preserved, and entrywise nonnegativity is checked after each product.

## 5. Supersolutions and contraction certificates

A matrix \(U\geq0\) satisfying

\[
F(U)\leq U
\tag{87.14}
\]

is called a supersolution for this fixed-point map. It need not solve the equation exactly. Because \(X_0=0\leq U\), monotonicity gives \(X_n\leq U\) for every iterate. Taking the limit proves \(X_\infty\leq U\). Combined with an iterate \(X_n\), this yields an entrywise enclosure of the least fixed point.

For a sharper norm error certificate, suppose \(F\) is a contraction with constant \(q<1\) on a set containing both an approximate matrix \(Z\) and the fixed point \(R\). Define the residual

\[
\delta=\|F(Z)-Z\|.
\]

Then

\[
\|R-Z\|
=\|F(R)-Z\|
\leq\|F(R)-F(Z)\|+\delta
\leq q\|R-Z\|+\delta,
\]

so

\[
\|R-Z\|\leq\frac{\delta}{1-q}.
\tag{87.15}
\]

For the polynomial map, if \(\|X\|,\|Y\|\leq M\) in a submultiplicative matrix norm, (87.3) gives the bound

\[
\|F(X)-F(Y)\|
\leq\left(\sum_{j=1}^{d}jM^{j-1}\|C_j\|\right)\|X-Y\|.
\tag{87.16}
\]

If the parenthesized constant is below one on an invariant region, it is a valid contraction constant. This may be conservative; failure of this test does not imply that the iteration diverges. Near critical queueing regimes, a contraction bound can become weak even when monotone lower and upper enclosures remain useful.

An upper certificate and a contraction certificate answer different questions. The supersolution gives componentwise order information about the least solution. The residual estimate gives a norm error bound when the map contracts. Neither should be substituted for the other without checking its hypotheses.

### Acceleration does not replace certification

The simple iteration can be slow when the derivative of the scalar map at its fixed point is close to one. Matrix-analytic algorithms therefore use Newton, cyclic reduction, or related accelerated methods. These methods can produce excellent candidates, but their iterates need not automatically remain nonnegative or below the least fixed point. Their convergence theorems require their own assumptions.

For the polynomial map, the Fréchet derivative at \(X\), applied to a perturbation \(H\), is

\[
DF_X[H]
=\sum_{j=1}^{d}\sum_{i=0}^{j-1}
X^i H X^{j-1-i}C_j.
\tag{87.19}
\]

This formula makes the Newton step a linear matrix equation in \(H\). A practical verified workflow can use an accelerated solver to propose a candidate, then use rational interval arithmetic to check a supersolution and bracket the least fixed point. If no contraction or order certificate is available, the candidate remains an approximation rather than a proof.

## 6. What changes with infinitely many downward jumps

For unbounded downward jumps, the rate map is an infinite series:

\[
F(X)=\sum_{j=0}^{\infty}X^jC_j.
\tag{87.17}
\]

The pointwise order argument still works for every finite partial sum. Passing to the infinite map requires convergence. To pass a monotone sequence \(X_n\uparrow X_\infty\) through the series, one needs a summable majorant, monotone convergence entrywise, or another theorem that justifies exchanging the limits and the sum.

One practical route is truncation. Let \(F_d(X)=\sum_{j=0}^{d}X^jC_j\). If \(\|X\|\leq M\), a bound on

\[
\sum_{j>d}M^j\|C_j\|
\tag{87.18}
\]

controls the omitted map terms. The norm bound must be valid on the region containing the iterates and the solution. A spectral-radius condition on the eventual solution alone does not guarantee that every chosen norm has \(\|X\|<1\). This is why the finite-support theorem is a useful formalization milestone before taking on infinite-support models.

## 7. Lean proof architecture

### 7.1 Encode the cone and the order

For a finite phase type, matrices over \(\mathbb R\) have finitely many entries. Define entrywise nonnegativity and order explicitly, or use the library order when its instance matches the intended pointwise relation. Prove reusable lemmas:

- nonnegative matrices are closed under addition and multiplication;
- \(X\leq Y\) and \(X,Y\geq0\) imply \(X^j\leq Y^j\);
- right multiplication by a nonnegative coefficient preserves order.

For the power lemma, induction with the difference identity (87.3) is often more robust than searching for a generic monotonicity theorem about matrix powers.

### 7.2 Separate sequence facts from matrix facts

Define the iteration by primitive recursion:

~~~lean
def rateIterate (F : Matrix Phase Phase ℝ → Matrix Phase Phase ℝ) :
    ℕ → Matrix Phase Phase ℝ
  | 0 => 0
  | n + 1 => F (rateIterate F n)
~~~

First prove its entrywise monotonicity and the bound by any nonnegative fixed point. Then project to a pair of phases \((i,j)\). Each coordinate is a monotone bounded real sequence, so it converges. Assemble the coordinate limits into a matrix and use continuity of finite sums and matrix multiplication to prove the fixed-point equation.

This coordinatewise route avoids needing a specialized order-completeness instance for matrices. Since the phase type is finite, converting the family of coordinate limits into matrix convergence is a finite-dimensional bookkeeping step.

More explicitly, for each pair of phases \((a,b)\), use the least upper bound of the bounded set \(\{(X_n)_{ab}:n\in\mathbb N\}\) as the limit entry. Monotonicity ensures this supremum is the sequential limit. Matrix addition and multiplication are finite sums of products of entries, so their continuity can be applied coordinate by coordinate. This gives a direct route to (87.7) without proving a general order-continuity theorem for an abstract matrix lattice.

### 7.3 Prove leastness by an invariant predicate

The leastness proof should quantify over an arbitrary nonnegative fixed point \(S\). Inductively maintain

\[
0\leq X_n\quad\text{and}\quad X_n\leq S.
\]

The fixed-point equation rewrites \(F(S)\) to \(S\), and monotonicity advances the bound. At the limit, pass the order relation entrywise. This proof architecture gives a theorem with a reusable statement:

> If \(S\) is any nonnegative fixed point, then the limit produced from zero is at most \(S\).

Do not prove leastness only against one certified upper matrix. The universal quantifier over fixed points is the mathematical content of minimality.

### 7.4 Keep computation outside the theorem

An executable program can calculate rational or interval approximations to \(X_n\), and a certificate can provide a candidate supersolution \(U\) or a residual bound. The core theorem should consume these values and verify their properties. This separation makes it possible to replace the numerical algorithm without changing the proof of leastness or the correctness of the enclosure.

The fixed-point theorem itself does not require an executable limit. It proves existence mathematically from completeness of the real numbers. A program that returns a finite iterate can still provide useful lower information, while an exact rational supersolution supplies an upper certificate.

## 8. Common failure modes

1. **Assuming fixed points are unique.** A nonlinear rate equation can have several nonnegative solutions; this theorem selects the least one.
2. **Iterating from an arbitrary matrix.** The monotonicity argument is anchored at zero and relies on a lower bound.
3. **Dropping nonnegativity.** Matrix products do not preserve entrywise order for arbitrary signed matrices.
4. **Commuting matrix factors.** The polynomial terms have a fixed order \(X^jC_j\).
5. **Taking limits before proving boundedness.** Existence of a fixed point supplies an upper bound for the iterates.
6. **Passing a limit through an infinite series without a theorem.** Finite support avoids this issue; infinite support needs summability or monotone convergence.
7. **Confusing least algebraic solution with a stationary queue.** Stability, boundary balance, and normalization remain separate.
8. **Treating a supersolution as an exact root.** \(F(U)\leq U\) is an enclosure certificate, not the fixed-point equation.
9. **Using a residual without contraction.** A small residual alone does not bound distance to a root.
10. **Assuming \(\rho(X)<1\) means \(\|X\|<1\).** This depends on the norm and may require a different scaling or a power bound.

## 9. Exercises

1. Prove (87.3) by induction without assuming that \(X\) and \(Y\) commute.
2. Show that \(F\) is monotone on the cone of nonnegative matrices.
3. Prove by induction that every iterate in (87.5) is bounded above by every nonnegative fixed point.
4. Complete the existence and leastness proof for \(X_\infty\), naming where finite support is used.
5. For (87.8), compute \(x_4\) exactly as a rational number and verify the bound \(x_4\leq0.15\).
6. Find a smaller rational supersolution than \(0.15\) for the scalar example and use it to narrow the bracket.
7. Verify the two-phase matrix products in Section 4 by hand or with exact rational arithmetic.
8. Derive (87.16) using the telescoping identity (87.3) and a submultiplicative norm.
9. State sufficient hypotheses under which a contraction residual gives a unique fixed point in a closed invariant set.
10. Extend the monotone iteration statement to an infinite coefficient sequence, explicitly identifying a theorem that justifies the limiting series.
11. Explain why the least fixed point may still fail to define a stationary probability distribution for the queue.
12. Design a Lean structure that stores a finite coefficient family, the monotone iterates, a fixed-point upper bound, and a rational enclosure.

## 10. Summary

With finite downward-jump support, the GI/M/1 rate equation is a polynomial map with nonnegative matrix coefficients. The map is monotone in entrywise order, so iteration from zero is increasing. Any nonnegative fixed point bounds every iterate; finite-dimensional completeness and polynomial continuity then give a least nonnegative fixed point as the limit.

The iterates provide lower bounds, and any nonnegative supersolution provides an upper bound. A contraction estimate can turn the residual into a norm error certificate. These results identify and enclose the algebraic rate matrix; positive recurrence and boundary normalization remain separate queueing theorems.

### Further reading

- M. F. Neuts, [“Markov chains with applications in queueing theory, which have a matrix-geometric invariant probability vector”](https://doi.org/10.2307/1426725), *Advances in Applied Probability* 10 (1978), 185–212. Neuts establishes the minimal nonnegative rate-matrix solution in the matrix-geometric invariant-vector setting.
- J. Pérez and B. Van Houdt, [“A fast Newton–Shamanskii iteration for M/G/1-type and GI/M/1-type Markov chains”](https://arxiv.org/abs/1508.06341), 2015. This paper studies faster iterative methods for the related minimal nonnegative matrix equations.
