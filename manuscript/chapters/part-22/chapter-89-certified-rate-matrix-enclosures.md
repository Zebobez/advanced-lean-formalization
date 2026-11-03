# Chapter 89 — Certified Enclosures for Rate Matrices

> **Audience.** This chapter assumes familiarity with matrix-geometric rate equations, monotone iteration, and Newton linearization. It combines order intervals with contraction estimates to certify a rate-matrix root and identify it as the least nonnegative solution.

A numerical solver can produce many digits of a plausible rate matrix. A formal proof needs a different object: a finite certificate that can be checked exactly and that proves the approximation encloses the intended root. Chapter 87 supplied monotone lower and upper bounds; Chapter 88 supplied Newton residuals and Jacobian information. Here we combine those ideas using a contraction on an invariant interval.

The method has two jobs. First, a fixed-point theorem proves that a unique root lies in a certified interval. Second, a monotone-iteration argument proves that this root is the least nonnegative solution required by the queueing model. The first job is analytic; the second is order-theoretic.

## Learning objectives

After this chapter, you should be able to:

- define an order interval of nonnegative matrices around a rate-matrix candidate;
- prove that the polynomial rate map preserves the interval;
- use a contraction bound and residual to enclose the unique fixed point;
- combine the enclosure with monotone iteration to prove leastness;
- package rational or interval data as checkable Lean certificates.

## 1. An interval for the rate equation

For a finite-support GI/M/1-type chain, write the rate equation as

\[
R=F(R),\qquad F(X)=\sum_{j=0}^{d}X^jC_j,
\tag{89.1}
\]

where each coefficient matrix \(C_j\) is nonnegative. The map \(F\) is monotone on the cone of nonnegative matrices, as proved in Chapter 87.

Choose matrices \(L,U\) with

\[
0\leq L\leq U.
\tag{89.2}
\]

The order interval between them is

\[
\mathcal I=[L,U]
=\{X:L\leq X\leq U\}.
\tag{89.3}
\]

Suppose the endpoints satisfy

\[
F(L)\geq L,\qquad F(U)\leq U.
\tag{89.4}
\]

For any \(X\in\mathcal I\), monotonicity gives

\[
L\leq F(L)\leq F(X)\leq F(U)\leq U.
\tag{89.5}
\]

Thus \(F\) maps \(\mathcal I\) into itself. The lower endpoint is a subsolution and the upper endpoint is a supersolution. An exact fixed point need not be either endpoint.

Because the phase space is finite, the matrix space is finite-dimensional and complete in any norm. The interval \(\mathcal I\) is closed, hence complete with the induced metric. This is the setting for the Banach fixed-point theorem.

## 2. Contraction gives a unique root in the interval

Assume there is a norm and a constant \(q<1\) such that

\[
\|F(X)-F(Y)\|\leq q\|X-Y\|
\qquad(X,Y\in\mathcal I).
\tag{89.6}
\]

Since \(F\) maps the complete set \(\mathcal I\) into itself and is a contraction there, it has a unique fixed point \(R_{\mathcal I}\) in \(\mathcal I\). The contraction iteration \(Z_{n+1}=F(Z_n)\), started from any point in \(\mathcal I\), converges to it.

For a candidate \(\widehat R\in\mathcal I\), define its fixed-point residual

\[
\delta=\|F(\widehat R)-\widehat R\|.
\tag{89.7}
\]

The unique fixed point satisfies

\[
\begin{aligned}
\|R_{\mathcal I}-\widehat R\|
&=\|F(R_{\mathcal I})-\widehat R\|\\
&\leq\|F(R_{\mathcal I})-F(\widehat R)\|+\delta\\
&\leq q\|R_{\mathcal I}-\widehat R\|+\delta.
\end{aligned}
\]

Rearranging yields the a posteriori error bound

\[
\|R_{\mathcal I}-\widehat R\|\leq\frac{\delta}{1-q}.
\tag{89.8}
\]

The residual by itself is not a certificate. The divisor \(1-q\) records how strongly residual error controls distance to the fixed point. If \(q\) is close to one, a small residual can still imply a wide enclosure.

### A convenient polynomial bound

Let the norm be submultiplicative, and suppose every matrix in the interval satisfies \(\|X\|\leq M\). The derivative formula from Chapter 87 gives

\[
\|DF_X[H]\|
\leq\left(\sum_{j=1}^{d}jM^{j-1}\|C_j\|\right)\|H\|.
\tag{89.9}
\]

The interval is convex, so the mean-value inequality shows that

\[
q=\sum_{j=1}^{d}jM^{j-1}\|C_j\|
\tag{89.10}
\]

is a valid contraction constant whenever it is below one. A sharper interval-specific estimate may reduce \(q\), but the simple bound is easy to verify. As always, \(\rho(R)<1\) does not imply \(\|R\|<1\) for every norm; establish the bound on the entire interval, not just at the unknown root.

## 3. Proving the interval root is the least root

The contraction theorem gives uniqueness only inside \(\mathcal I\). A queueing rate equation may have other nonnegative fixed points outside it. To identify the intended solution, choose the lower endpoint to be an iterate from Chapter 87:

\[
L=X_N,\qquad X_0=0,\qquad X_{n+1}=F(X_n).
\tag{89.11}
\]

Let \(U\) be a nonnegative supersolution, so \(F(U)\leq U\), and choose \(U\) with \(L\leq U\). Then the monotone sequence \(X_n\) remains below \(U\), and its limit is the least nonnegative fixed point \(R_{\min}\). Since \(L=X_N\), the tail sequence

\[
X_N,\ X_{N+1},\ X_{N+2},\ldots
\]

is precisely the iteration of \(F\) starting at \(L\). It remains in \([L,U]\) and converges to \(R_{\min}\). But the contraction theorem says that every iteration starting in this interval converges to the unique fixed point \(R_{\mathcal I}\). Therefore

\[
R_{\min}=R_{\mathcal I}.
\tag{89.12}
\]

This final step is what converts a local uniqueness result into a least-root certificate. Merely finding one root in a small box does not show that it is the matrix-geometric rate matrix.

## 4. Worked example: a scalar certified enclosure

Consider again

\[
F(x)=0.1+0.2x+0.7x^2.
\tag{89.13}
\]

The least fixed point is \(1/7\). Chapter 87's iterates start at \(x_0=0\), with

\[
x_1=0.1,\quad x_2=0.127,\quad x_3=0.1366903,\quad x_4=F(x_3).
\]

The exact value is

\[
x_4=\frac{140417026679863}{10^{15}}
=0.140417026679863,
\]

so \(0.14<x_4<0.15\). Set

\[
L=x_4,\qquad U=0.15.
\]

The lower condition \(F(L)\geq L\) holds because \(L\) is an iterate. The upper condition is checked exactly:

\[
F(U)=0.14575\leq0.15=U.
\tag{89.14}
\]

On \([L,U]\), the derivative is \(F'(x)=0.2+1.4x\), so

\[
0\leq F'(x)\leq0.41<1.
\tag{89.15}
\]

The map is therefore a contraction of this interval into itself. The Banach theorem gives a unique fixed point in the interval; the iterate argument proves it is the least nonnegative root.

Take \(\widehat x=0.145\). Its residual is

\[
|F(\widehat x)-\widehat x|
=|0.1437175-0.145|
=0.0012825.
\]

Using \(q=0.41\), (89.8) gives

\[
|x_{\min}-0.145|
\leq\frac{0.0012825}{0.59}<0.00218.
\tag{89.16}
\]

The residual and the contraction constant are rational numbers, so the final inequality can be verified exactly. The interval \([L,U]\) may give a tighter bound than the residual estimate; both are useful certificates, and their intersection is also a valid enclosure.

### A two-phase rational certificate

Consider the affine matrix map

\[
F(X)=C_0+XC_1,\qquad
C_0=\begin{pmatrix}0.08&0.01\\0.02&0.07\end{pmatrix},
\quad
C_1=\begin{pmatrix}0.2&0.1\\0&0.2\end{pmatrix}.
\tag{89.17}
\]

This illustrates the certificate algebra; the coefficients alone are not presented as a complete stochastic queue model. Use the induced infinity norm, the maximum absolute row sum. Then \(\|C_1\|_\infty=0.3\), and

\[
\|F(X)-F(Y)\|_\infty
=\|(X-Y)C_1\|_\infty
\leq0.3\|X-Y\|_\infty.
\]

Take \(L=0\) and

\[
U=\begin{pmatrix}0.13&0.05\\0.04&0.12\end{pmatrix}.
\]

Direct rational multiplication gives

\[
F(U)=\begin{pmatrix}0.106&0.033\\0.028&0.098\end{pmatrix}
\leq U,
\]

while \(F(L)=C_0\geq L\). Hence the interval is invariant and the map is a contraction there. The unique fixed point can also be computed exactly as

\[
R=C_0(I-C_1)^{-1}
=\begin{pmatrix}1/10&1/40\\1/40&29/320\end{pmatrix}.
\]

Now let

\[
\widehat R=\begin{pmatrix}0.1&0.025\\0.025&0.09\end{pmatrix}.
\]

This candidate is inside the interval, and its residual is

\[
F(\widehat R)-\widehat R
=\begin{pmatrix}0&0\\0&0.0005\end{pmatrix},
\qquad
\|F(\widehat R)-\widehat R\|_\infty=\frac1{2000}.
\]

The contraction estimate certifies

\[
\|R-\widehat R\|_\infty
\leq\frac{1/2000}{1-0.3}
=\frac1{1400}.
\]

All endpoint checks, products, and residual bounds involve rational numbers. This is the form of evidence a Lean theorem can verify without trusting the code that discovered the candidate.

### 4.1 An executable two-phase rational certificate

The code instantiates the affine map with the matrices from Section 4. It checks the nonnegative coefficients, the contraction norm (3/10), the supersolution endpoint, and that both the candidate and exact fixed point lie in the box. It computes the residual as a matrix with only one nonzero entry, verifies its induced infinity norm (1/2000), and checks the resulting residual bound (1/1400). These rational checks are the finite data for a Banach fixed-point certificate; the generic contraction theorem remains a separate result.

```lean
abbrev EnclosureMatrix := Matrix (Fin 2) (Fin 2) ℚ

def enclosureC0 : EnclosureMatrix := !![2 / 25, 1 / 100; 1 / 50, 7 / 100]
def enclosureC1 : EnclosureMatrix := !![1 / 5, 1 / 10; 0, 1 / 5]
def enclosureUpper : EnclosureMatrix := !![13 / 100, 1 / 20; 1 / 25, 3 / 25]
def enclosureCandidate : EnclosureMatrix := !![1 / 10, 1 / 40; 1 / 40, 9 / 100]
def enclosureRoot : EnclosureMatrix := !![1 / 10, 1 / 40; 1 / 40, 29 / 320]

def affineRateMap (X : EnclosureMatrix) : EnclosureMatrix := enclosureC0 + X * enclosureC1

def matrixInfinityNorm2 (A : EnclosureMatrix) : ℚ :=
  max (∑ j : Fin 2, |A 0 j|) (∑ j : Fin 2, |A 1 j|)

def enclosureResidual : EnclosureMatrix :=
  affineRateMap enclosureCandidate - enclosureCandidate

theorem enclosureC0_nonnegative : ∀ i j : Fin 2, 0 ≤ enclosureC0 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [enclosureC0]

theorem enclosureC1_nonnegative : ∀ i j : Fin 2, 0 ≤ enclosureC1 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [enclosureC1]

theorem enclosureC1_infinity_norm : matrixInfinityNorm2 enclosureC1 = 3 / 10 := by
  norm_num [matrixInfinityNorm2, enclosureC1]

theorem enclosure_upper_supersolution :
    ∀ i j : Fin 2, affineRateMap enclosureUpper i j ≤ enclosureUpper i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [affineRateMap, enclosureC0, enclosureC1, enclosureUpper,
      Matrix.add_apply, Matrix.mul_apply]

theorem enclosure_candidate_in_box :
    (∀ i j : Fin 2, 0 ≤ enclosureCandidate i j) ∧
      (∀ i j : Fin 2, enclosureCandidate i j ≤ enclosureUpper i j) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [enclosureCandidate, enclosureUpper]

theorem enclosure_root_is_fixed : affineRateMap enclosureRoot = enclosureRoot := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [affineRateMap, enclosureC0, enclosureC1, enclosureRoot,
      Matrix.add_apply, Matrix.mul_apply]

theorem enclosure_root_in_box :
    (∀ i j : Fin 2, 0 ≤ enclosureRoot i j) ∧
      (∀ i j : Fin 2, enclosureRoot i j ≤ enclosureUpper i j) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [enclosureRoot, enclosureUpper]

theorem enclosure_residual_exact :
    enclosureResidual = !![0, 0; 0, (1 : ℚ) / 2000] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [enclosureResidual, affineRateMap, enclosureC0, enclosureC1,
      enclosureCandidate, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]

theorem enclosure_residual_norm : matrixInfinityNorm2 enclosureResidual = 1 / 2000 := by
  rw [enclosure_residual_exact]
  norm_num [matrixInfinityNorm2]

theorem enclosure_contraction_factor_lt_one : (3 / 10 : ℚ) < 1 := by norm_num

theorem enclosure_residual_error_bound :
    (1 / 2000 : ℚ) / (1 - 3 / 10) = 1 / 1400 := by
  norm_num
```

## 5. Matrix certificates with rational endpoints

For an \(m\times m\) rate matrix, choose rational matrices \(L,U,\widehat R\). To check the order conditions, compare every entry exactly. To check the subsolution and supersolution conditions:

1. evaluate the polynomial \(F(L)\) and \(F(U)\) using rational matrix arithmetic;
2. verify \(L\leq F(L)\) and \(F(U)\leq U\) entrywise;
3. prove that the entire interval has norm at most \(M\);
4. verify the coefficient bound in (89.10) is below one;
5. evaluate the residual \(F(\widehat R)-\widehat R\);
6. apply (89.8) using a certified norm bound.

No floating-point result is trusted. A numerical library may discover good endpoints, but the proof assistant checks the rational inequalities. For irrational coefficients, use rational interval enclosures for each coefficient and propagate them through the matrix operations with directed rounding. The interval arithmetic theorem must account for each multiplication; simply printing decimal digits is not enough.

The choice of norm controls the shape and cost of the certificate. An induced infinity norm can be bounded by maximum absolute row sums, which are straightforward to verify entrywise. A weighted norm may yield a smaller contraction constant, but it introduces additional weights and positivity conditions. Use the simplest norm that proves \(q<1\); optimize the certificate only when the basic bound is too weak.

### Propagating the enclosure to queue performance

A certified rate-matrix interval can also bound the outputs from Chapter 85. Suppose \(0\leq L\leq R\leq U\) and \(U\) has norm less than one in a submultiplicative norm. Then every power is ordered:

\[
L^n\leq R^n\leq U^n.
\]

Summing the nonnegative terms gives resolvent bounds

\[
(I-L)^{-1}\leq(I-R)^{-1}\leq(I-U)^{-1}.
\]

For a fixed nonnegative boundary row \(\pi_0\), multiplying by \(\pi_0\) and the all-ones column encloses the tail probability \(\pi_0R^K(I-R)^{-1}\mathbf1\). The same termwise argument bounds the mean-level series \(\pi_0\sum_{n\geq0}nR^n\mathbf1\). If the boundary vector also depends on \(R\), it needs its own certified enclosure; treating it as fixed would omit part of the error.

### Reporting the enclosure

If the certificate uses the induced infinity norm and proves \(\|R-\widehat R\|_\infty\leq\epsilon\), then every entry satisfies

\[
|R_{ij}-\widehat R_{ij}|\leq\epsilon.
\]

Each computed matrix entry can therefore be reported as an interval, intersected with the order interval \([L,U]\) when that is tighter. When converting rational endpoints to decimal output, round lower endpoints downward and upper endpoints upward. Ordinary round-to-nearest display can exclude the exact value even when the internal rational certificate is sound.

For a different norm, include the conversion constant from that norm to the entrywise maximum norm. This makes the printed precision part of the theorem statement: readers can see exactly which digits are certified, rather than inferring accuracy from the number of digits returned by a solver.

## 6. Lean formalization architecture

### 6.1 Define a closed order interval

For finite phases, define the interval by the predicates \(L\leq X\) and \(X\leq U\), together with nonnegativity if it is not already implied by \(L\geq0\). Prove:

- the interval is nonempty when \(L\leq U\);
- it is closed in the chosen matrix norm;
- it is complete as a subtype of the complete matrix space;
- monotonicity and the endpoint inequalities make \(F\) a self-map.

Keep the order interval separate from the metric ball. The order endpoints establish positivity and root selection; the norm establishes contraction.

### 6.2 Package the contraction hypotheses

A certificate structure can store:

- the coefficient family and finite support bound;
- endpoints \(L,U\) and their entrywise order proofs;
- the endpoint inequalities \(F(L)\geq L\) and \(F(U)\leq U\);
- a norm bound \(M\) and contraction constant \(q<1\);
- a candidate \(\widehat R\) inside the interval;
- a residual upper bound \(\delta\).

The main theorem should return a unique fixed point in the interval, leastness when \(L\) is a monotone iterate, and the distance estimate \(\|R-\widehat R\|\leq\delta/(1-q)\). Separate the existence theorem from the residual theorem so that callers can use whichever conclusion they need.

### 6.3 Verify the arithmetic independently

When all certificate entries are rational, the checks for endpoint inequalities and residual bounds reduce to exact rational arithmetic. Norm estimates such as maximum row sums can also be reduced to finitely many rational inequalities. The Banach fixed-point theorem remains the analytic engine, but the model-specific evidence passed to it is finite and checkable.

For interval-valued coefficients, use a verified interval type with outward rounding. The proof should distinguish:

- the mathematical coefficient matrix;
- an interval enclosing each coefficient;
- the interval result enclosing each matrix product;
- the final inequality that establishes \(F([L,U])\subseteq[L,U]\).

This bookkeeping prevents a common gap in computer-assisted proofs: a numerical enclosure is only meaningful if every arithmetic operation has a proved containment theorem.

### 6.4 Keep the certificate small

The solver may use high precision, preconditioning, Newton corrections, or heuristic search to discover \(L,U,\widehat R\). The formal checker need not replay those steps. It verifies the final rational or interval certificate and applies general theorems. This makes the proof robust to changes in software and allows independent implementations to produce certificates for the same theorem.

## 7. Common failure modes

1. **Using a residual without a contraction bound.** The residual alone does not control the distance to a root.
2. **Proving a root exists but not identifying it.** Local uniqueness does not imply global minimality.
3. **Using an arbitrary lower endpoint.** For leastness, \(L\) must lie below the least root; a known monotone iterate guarantees this.
4. **Checking only endpoint fixed-point residuals.** Interval invariance requires the ordered inequalities \(F(L)\geq L\) and \(F(U)\leq U\).
5. **Bounding the derivative only at the candidate.** The contraction estimate must hold throughout the interval.
6. **Assuming \(\|R\|<1\) from \(\rho(R)<1\).** Verify the norm bound on the full interval.
7. **Trusting floating-point endpoints.** Convert them to rational or outward-rounded interval data and prove each inequality.
8. **Ignoring the norm's compatibility with matrix products.** The polynomial Lipschitz estimate uses submultiplicativity.
9. **Applying Banach to a non-complete set.** Use a closed interval in a complete finite-dimensional space.
10. **Confusing a supersolution with an exact rate matrix.** The endpoint only bounds the least fixed point.

## 8. Exercises

1. Prove the interval invariance implication (89.5) from monotonicity and the endpoint inequalities.
2. Prove the residual estimate (89.8) directly from the contraction inequality.
3. Show that the Chapter 87 iterate \(X_N\) is a valid lower endpoint for a least-root certificate.
4. For the scalar example, express \(x_4\) as an exact rational number and verify \(0.14<x_4<0.15\).
5. Verify the contraction constant \(0.41\) on \([x_4,0.15]\).
6. Compute the residual at \(\widehat x=0.145\) exactly and check the bound in (89.16).
7. Give a matrix example where a norm bound at the candidate is below one but a larger interval makes the simple coefficient bound exceed one.
8. Design a Lean certificate structure for a two-phase polynomial rate map with rational coefficients.
9. Explain how to prove leastness if the lower endpoint is not itself an iterate but is separately shown to be below the least fixed point.
10. Extend the interval certificate to coefficients given by rational enclosures.
11. Compare the information returned by an entrywise interval and by a norm residual bound.
12. Explain why the contraction theorem can fail to prove uniqueness even when the rate equation still has a unique least nonnegative solution.

## 9. Summary

An invariant order interval \(L\leq X\leq U\), combined with a contraction bound, provides a finite certificate for a unique rate-equation root. A residual at a candidate then gives the explicit distance bound \(\delta/(1-q)\). Choosing \(L\) from monotone iteration and \(U\) as a supersolution identifies the interval root with the least nonnegative fixed point.

The method separates numerical discovery from formal verification. The solver proposes rational or interval data; Lean checks endpoint inequalities, contraction constants, and residual bounds, then applies completeness and fixed-point theorems. The result is both an enclosure of the rate matrix and a proof that it is the rate matrix required by the matrix-geometric stationary law.

### Further reading

- M. F. Neuts, [“Markov chains with applications in queueing theory, which have a matrix-geometric invariant probability vector”](https://doi.org/10.2307/1426725), *Advances in Applied Probability* 10 (1978), 185–212. This paper establishes the minimal nonnegative rate-matrix framework.
- J. Pérez and B. Van Houdt, [“A fast Newton–Shamanskii iteration for M/G/1-type and GI/M/1-type Markov chains”](https://arxiv.org/abs/1508.06341), 2015. This paper studies accelerated methods for computing minimal nonnegative solutions.
