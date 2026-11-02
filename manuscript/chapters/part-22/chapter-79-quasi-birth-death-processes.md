# Chapter 79 — Quasi-Birth–Death Processes and Matrix-Analytic Methods

> **Audience.** This chapter assumes familiarity with continuous-time Markov chains, generators, stationary distributions, and birth–death processes. It replaces scalar level recurrences with finite-dimensional matrix equations, and shows how a repeating block structure can turn an infinite stationary problem into a quadratic equation for a rate matrix.

A birth–death chain has one state at each level and can move only to a neighboring level. A quasi-birth–death process (QBD) keeps the nearest-neighbor movement between levels but gives each level a finite collection of phases. The level may represent the number of customers in a queue; the phase can record the state of a service mechanism, a modulating environment, or a finite control mode.

The payoff is a matrix-geometric stationary tail. Once the repeating interior has been encoded by three finite matrices, stationary probabilities at successive levels are related by multiplication by a single rate matrix. This chapter derives that relation carefully, including the matrix order, the exceptional boundary equations, and the stability condition needed to normalize the resulting tail.

## Learning objectives

After this chapter, you should be able to:

- describe a level-and-phase state space and its block-tridiagonal generator;
- derive the interior stationary recurrence from the row-generator convention;
- obtain the matrix quadratic equation for a geometric rate matrix;
- keep boundary equations separate from the repeating interior;
- check geometric summability and normalize the stationary distribution;
- organize a Lean development around finite block certificates and a countable-state invariant law.

## 1. Levels, phases, and repeated local structure

Let the phase type be a finite type *Phase*. The state space is

\[
\mathbb{N}\times \mathrm{Phase}.
\]

The first coordinate is the level and the second is the phase. In a queue, level zero often means an empty system. The interior levels \(n\geq 1\) all use the same transition rules:

- an upward move from level \(n\) to \(n+1\), described by a matrix \(A_1\);
- a move that stays at level \(n\), including phase changes, described by \(A_0\);
- a downward move from level \(n\) to \(n-1\), described by a matrix \(A_{-1}\).

Each block is indexed by the source phase in its rows and the destination phase in its columns. In particular, all three blocks are Phase-by-Phase matrices. The diagonal entries of \(A_0\) include the negative total rates leaving a state; its off-diagonal entries describe within-level phase changes.

The boundary need not obey the interior rule. Write \(B_{00}\) for the level-zero-to-level-zero block, \(B_{01}\) for level zero to level one, and \(B_{10}\) for level one to level zero. A common QBD generator has the schematic form

~~~text
             level 0     level 1     level 2     level 3     ...
level 0       B00         B01           0           0
level 1       B10          A0           A1          0
level 2         0          A-1          A0          A1
level 3         0           0           A-1         A0        A1
  ...
~~~

The block matrix is tridiagonal in the level coordinate and translation-invariant above the boundary. That combination—finite phase space and a repeated nearest-neighbor interior—is the defining structure used by the matrix-geometric method.

For a valid generator, off-diagonal rates are nonnegative and every full row sums to zero. Individual blocks need not have row sums zero: the rate leaving a block is balanced by rates in other blocks. The interior row-sum identity is

\[
A_{-1}\mathbf{1}+A_0\mathbf{1}+A_1\mathbf{1}=0.
\]

This identity is a useful sanity check, but it is not a substitute for entrywise nonnegativity of off-diagonal transition rates.

## 2. The stationary equations by level

Let \(\pi_n\) be the row vector of stationary masses at level \(n\). Its \(i\)-th component is the probability of being at level \(n\) in phase \(i\). The row-vector convention is important: stationarity is written as \(\pi Q=0\), so a source block multiplies on the right.

At an interior target level \(n\geq 2\), probability flows in from level \(n-1\), level \(n\), and level \(n+1\). The balance equation is

\[
\pi_{n-1}A_1+\pi_nA_0+\pi_{n+1}A_{-1}=0.
\tag{79.1}
\]

The first term uses \(A_1\) because it describes transitions from the lower source level \(n-1\) into level \(n\). The last term uses \(A_{-1}\) because it describes transitions from the higher source level \(n+1\) down to level \(n\). Reading the blocks by target rather than source is a common way to reverse these terms.

The two boundary equations are different:

\[
\pi_0B_{00}+\pi_1B_{10}=0,
\tag{79.2}
\]

\[
\pi_0B_{01}+\pi_1A_0+\pi_2A_{-1}=0.
\tag{79.3}
\]

Equation (79.2) balances level zero. Equation (79.3) balances level one, which receives upward transitions from level zero but otherwise uses interior blocks. A model may require a special within-level block at level one; in that case replace \(A_0\) there by its actual boundary block. Never infer the boundary equations by blindly extending (79.1) to level zero.

Balance equations are local. To identify a stationary probability distribution, we will also need nonnegative entries and total mass one. For a countable-state continuous-time chain, one must additionally have a well-defined non-explosive process; a QBD with a fixed finite set of bounded rate blocks has uniformly bounded exit rates and is non-explosive.

## 3. The matrix-geometric ansatz

The interior equations repeat at every sufficiently high level. It is therefore reasonable to look for a solution whose level vectors change by the same linear transformation at each step. Let \(R\) be a square matrix on the phase space and posit

\[
\pi_n=\pi_1R^{n-1},\qquad n\geq 1.
\tag{79.4}
\]

The exponent is zero at level one, so \(\pi_1=\pi_1I\). For level two, \(\pi_2=\pi_1R\); for level three, \(\pi_3=\pi_1R^2\).

Substitute (79.4) into (79.1):

\[
\begin{aligned}
0
&=\pi_1R^{n-2}A_1+\pi_1R^{n-1}A_0+\pi_1R^nA_{-1}\\
&=\pi_1R^{n-2}\bigl(A_1+RA_0+R^2A_{-1}\bigr).
\end{aligned}
\]

Thus a sufficient condition for every interior equation is the matrix quadratic equation

\[
A_1+RA_0+R^2A_{-1}=0.
\tag{79.5}
\]

The order in (79.5) is determined by the chosen convention. The row distribution multiplies the blocks from the left, and the powers of \(R\) appear before the blocks when the repeated factor is extracted. Matrix multiplication is not commutative: neither \(A_0R\) nor \(A_{-1}R^2\) is interchangeable with the displayed expression.

Under the standard irreducibility and stability hypotheses for a QBD, the relevant rate matrix is the minimal nonnegative solution of (79.5). “Nonnegative” means entrywise nonnegative, not positive semidefinite. Minimality is entrywise order: among nonnegative solutions, the chosen solution has no larger entry than any other solution. It selects the tail associated with the stochastic process rather than an algebraic branch of the matrix polynomial. The name “rate matrix” is conventional here; \(R\) is the geometric tail factor, not a continuous-time generator.

The word “sufficient” above matters. The matrix equation implies the recurrence after multiplication by \(\pi_1R^{n-2}\). The recurrence alone, for one particular \(\pi_1\), does not necessarily imply the whole matrix equation: the row vector may fail to detect some directions in phase space. Formal proofs should preserve this distinction.

## 4. Boundary conditions determine the starting vector

The matrix \(R\) controls how mass propagates after level one. It does not determine \(\pi_0\) and \(\pi_1\) by itself. The boundary equations select the initial row vectors.

Using \(\pi_2=\pi_1R\), equation (79.3) becomes

\[
\pi_0B_{01}+\pi_1A_0+\pi_1RA_{-1}=0.
\tag{79.6}
\]

Together, the boundary balance equations and the geometric relation constrain \(\pi_0\) and \(\pi_1\). In some models they can be solved linearly after \(R\) has been computed. The remaining scalar degree of freedom is fixed by normalization.

This separation suggests a clean proof architecture:

1. establish that the three interior blocks describe a valid repeated generator;
2. establish that \(R\) solves (79.5) and is entrywise nonnegative;
3. use (79.4) to define the positive-level row vectors;
4. prove all interior balance equations by a matrix identity;
5. prove the two boundary equations for \(\pi_0,\pi_1\);
6. prove finite total mass and normalize;
7. invoke an appropriate theorem connecting the resulting invariant law to the chain.

The proof is modular because each step has one role. In Lean, this organization prevents the matrix polynomial, boundary algebra, infinite sum, and Markov-process theorem from being entangled in one large goal.

## 5. Stability and the geometric series

For the geometric tail to have finite mass, the powers of \(R\) must be summable. A standard sufficient condition is that the spectral radius satisfy

\[
\rho(R)<1.
\tag{79.7}
\]

Then the matrix geometric series converges:

\[
\sum_{k=0}^{\infty}R^k=(I-R)^{-1}.
\tag{79.8}
\]

Consequently, the total mass on positive levels is

\[
\sum_{n=1}^{\infty}\pi_n\mathbf{1}
=\sum_{k=0}^{\infty}\pi_1R^k\mathbf{1}
=\pi_1(I-R)^{-1}\mathbf{1}.
\tag{79.9}
\]

The normalization equation is therefore

\[
\pi_0\mathbf{1}+\pi_1(I-R)^{-1}\mathbf{1}=1.
\tag{79.10}
\]

This expression is meaningful only after convergence has been established. Writing down an inverse does not prove that the nonnegative level masses sum to a finite value. Nor does a formal algebraic identity for \((I-R)^{-1}\) alone establish convergence of the infinite series.

For an irreducible QBD with finite phases and standard regularity assumptions, positive recurrence is characterized by negative mean drift in the level coordinate under the stationary distribution of the background phase process. If

\[
S=A_{-1}+A_0+A_1
\]

is the phase generator in the homogeneous interior and \(\alpha S=0\), \(\alpha\mathbf 1=1\), then the mean level drift is

\[
\alpha(A_1-A_{-1})\mathbf{1}.
\tag{79.11}
\]

Negative drift yields stability in the usual irreducible setting. This criterion is often easier to interpret than (79.7), while the spectral-radius condition is directly suited to summing the matrix-geometric tail. A formal development should state the hypotheses of the drift theorem it uses; the drift formula alone is not a proof of positive recurrence.

## 6. Worked example: the M/M/1 queue

An M/M/1 queue has one phase, so each block is a scalar. Let \(\lambda\) be the arrival rate and \(\mu\) the service rate. In the interior,

\[
A_1=\lambda,\qquad A_0=-(\lambda+\mu),\qquad A_{-1}=\mu.
\]

The quadratic equation (79.5) is

\[
\lambda-(\lambda+\mu)R+\mu R^2=0.
\]

It factors as

\[
(\mu R-\lambda)(R-1)=0,
\]

so the algebraic roots are \(R=\lambda/\mu\) and \(R=1\). In the stable case \(\lambda<\mu\), the minimal nonnegative solution with value below one is

\[
R=\varrho=\frac{\lambda}{\mu}.
\]

At level zero, arrivals leave the empty state at rate \(\lambda\). At level one, a service completion returns to level zero at rate \(\mu\). The boundary equation is

\[
\lambda\pi_0-\mu\pi_1=0,
\]

so \(\pi_1=\varrho\pi_0\). The matrix-geometric formula gives \(\pi_n=\pi_1\varrho^{n-1}\) for all \(n\geq1\). Normalization yields

\[
1=\pi_0+\sum_{n=1}^{\infty}\pi_1\varrho^{n-1}
=\pi_0+\frac{\pi_1}{1-\varrho},
\]

and hence

\[
\pi_n=(1-\varrho)\varrho^n,\qquad n\geq0.
\]

This familiar scalar result is a diagnostic for every matrix convention in the chapter. If the chosen block orientation or exponent produces the wrong scalar quadratic, a block has been transposed or the incoming and outgoing blocks have been swapped.

At \(\lambda=\mu\), the candidate root is one and the geometric series diverges. At \(\lambda>\mu\), the root \(\lambda/\mu\) exceeds one, so no normalized geometric stationary law results. The stability condition is not a cosmetic add-on: it distinguishes a stationary distribution from a merely formal solution of the balance recurrence.

## 7. Worked example: a Markov-modulated queue

Consider a single-server queue whose service rate depends on a two-state environment. The environment changes from phase 0 to phase 1 at rate \(\alpha\), and from phase 1 to phase 0 at rate \(\beta\). Arrivals occur at rate \(\lambda\) in either phase. Service rates are \(\mu_0\) and \(\mu_1\). Let

\[
S=\begin{pmatrix}-\alpha&\alpha\\ \beta&-\beta\end{pmatrix},
\qquad
M=\begin{pmatrix}\mu_0&0\\0&\mu_1\end{pmatrix}.
\]

For levels \(n\geq1\), the repeated blocks are

\[
A_1=\lambda I,\qquad A_{-1}=M,\qquad
A_0=S-\lambda I-M.
\]

The equality \(A_{-1}+A_0+A_1=S\) confirms that the environment evolves according to \(S\) when level changes are ignored. The rate matrix satisfies

\[
\lambda I+R(S-\lambda I-M)+R^2M=0.
\tag{79.12}
\]

This is genuinely matrix-valued. Unless the environment and service structure have special symmetries, the entries of \(R\) are not captured by a single ratio \(\lambda/\mu\). An arrival preserves the environment phase, while an environment switch may occur without changing the level, so the stationary tail records how phase and queue length interact.

At level zero, no service completion can occur. The boundary blocks are

\[
B_{00}=S-\lambda I,\qquad B_{01}=\lambda I,\qquad B_{10}=M.
\]

The stationary boundary equations are therefore

\[
\pi_0(S-\lambda I)+\pi_1M=0,
\]

\[
\pi_0\lambda I+\pi_1(S-\lambda I-M)+\pi_2M=0.
\]

Once \(R\) and the boundary vectors are determined, the positive-level tail is \(\pi_n=\pi_1R^{n-1}\). The environment stationary row vector is

\[
\alpha=\left(\frac{\beta}{\alpha+\beta},\frac{\alpha}{\alpha+\beta}\right).
\]

The mean drift condition becomes

\[
\lambda-\left(\frac{\beta\mu_0+\alpha\mu_1}{\alpha+\beta}\right)<0.
\]

This gives a compact stability check, although computing performance measures such as the mean queue length still requires the matrix tail and its derivatives or matrix moments. The example also demonstrates why boundary blocks deserve their own names: inserting a service block at level zero would describe a different process.

## 8. Generating functions and tail observables

The matrix-geometric representation packages more than normalization. Define a row-vector generating function

\[
\Pi(z)=\sum_{n=1}^{\infty}\pi_nz^{n-1}.
\]

When the series converges,

\[
\Pi(z)=\pi_1\sum_{k=0}^{\infty}(zR)^k
=\pi_1(I-zR)^{-1}.
\tag{79.13}
\]

The scalar probability-generating function for the positive-level mass is \(\Pi(z)\mathbf 1\), with the level-zero term added separately if the convention is to count level zero as \(z^0\). Differentiating at \(z=1\), when the needed moments are finite, yields moments of the level. For example,

\[
\sum_{n=1}^{\infty} n\pi_n\mathbf 1
=\pi_1(I-R)^{-2}\mathbf 1
\]

under the standard convergence assumptions. Be precise about the power convention: \(\Pi(z)\) uses exponent \(n-1\), while the queue length itself is \(n\). A derivative with respect to \(z\) first produces \(n-1\), so a shift is required when reporting the expected level.

The generating-function viewpoint offers another route to derive stationary equations. It is useful for analytic transforms, while the matrix-geometric representation is often convenient for numerical computation and tail probabilities. These are related methods, but they impose different proof obligations: a formal power series identity, analytic convergence, or a matrix fixed-point certificate.

## 9. A Lean proof architecture

The mathematical state space is countable, but the repeated local data are finite-dimensional. A Lean development should make that distinction visible. Use a finite phase type for block matrices and retain the natural number level as the unbounded coordinate. A row distribution at one level can be represented as a function from Phase to real numbers; a block is a function from Phase to functions from Phase to real numbers, or an equivalent matrix type.

Separate the definitions and lemmas into layers:

### 9.1 Block-level algebra

Prove finite-dimensional facts about nonnegativity, row sums, and matrix multiplication. These lemmas know nothing about the Markov process. For example, establish that if \(R\) solves (79.5), then the geometric vectors \(\pi_1R^k\) satisfy every translated interior recurrence. This proof is algebraic and uses associativity and distributivity, not probability theory.

### 9.2 Boundary and normalization certificates

Keep \(\pi_0\), \(\pi_1\), \(B_{00}\), \(B_{01}\), and \(B_{10}\) explicit. Prove the boundary equations separately. Then prove that every component of each \(\pi_n\) is nonnegative from nonnegativity of \(\pi_1\) and \(R\). Finally, use a theorem about convergent matrix series or a scalar majorant to establish (79.9) and (79.10).

Do not encode “\(R\) is the right answer” as an opaque assumption if the goal is to verify a numerical certificate. Expose the properties the proof actually consumes:

- entrywise nonnegativity of \(R\);
- the matrix quadratic equation;
- a spectral-radius or norm bound implying summability;
- the boundary equations;
- total mass one.

Minimality may be important for the mathematical identification of the rate matrix, but it is not needed to verify that a supplied \(R\), together with the other certificates, produces a stationary candidate. This distinction can shorten the verification layer.

### 9.3 Countable-state probability

The final layer connects level blocks to a probability measure on \(\mathbb N\times\mathrm{Phase}\). Prove that the masses sum to one, then show invariance using the generator or transition semigroup theorem available in the chosen library setup. State the regularity assumptions needed for that theorem. Because the repeated finite blocks have bounded rates, non-explosion is accessible, but the proof still needs to connect the chosen generator representation to the process semantics.

If the development begins with finite approximations, do not silently identify the stationary law of a truncated chain with that of the infinite QBD. Truncation changes the top boundary. A convergence theorem is needed before a finite-capacity computation can justify an infinite-state claim.

## 10. Common failure modes

1. **Reversing source and target blocks.** The balance equation at target level \(n\) receives from \(n-1\) through \(A_1\) and from \(n+1\) through \(A_{-1}\).
2. **Changing matrix order.** The row convention gives \(A_1+RA_0+R^2A_{-1}=0\). Matrices do not commute.
3. **Extending the interior equation to the boundary.** Level zero has different physical transitions, especially in queues where service is disabled when empty.
4. **Selecting an arbitrary polynomial root.** The stationary rate matrix is the relevant minimal nonnegative solution under the model's hypotheses.
5. **Treating \(R\) as stochastic.** It is a nonnegative rate matrix in the geometric representation, not generally a transition matrix; its row sums need not equal one.
6. **Normalizing before proving convergence.** Equation (79.10) requires a summable tail, commonly guaranteed by \(\rho(R)<1\).
7. **Proving only balance and claiming uniqueness.** Invariance, non-explosion, irreducibility, and positive recurrence are separate issues.
8. **Using a scalar intuition for phase interactions.** In the modulated example, arrivals, service, and phase switching affect different entries and need not collapse to one effective rate ratio.

## 11. Exercises

1. **Check the block recurrence.** Starting from (79.4), substitute into (79.1) and show explicitly how the factor \(R^{n-2}\) appears. State the minimum level at which the derivation applies.
2. **Find the scalar roots.** Factor the M/M/1 quadratic and explain why the root equal to one is not a summable stationary tail.
3. **Boundary audit.** Write the three boundary blocks for an M/M/1/K queue with finite capacity \(K\). Identify which upward transitions disappear at level \(K\), and explain why this is not the same infinite QBD.
4. **Drift calculation.** For the two-phase modulated queue, derive the stationary phase vector \(\alpha\) and the mean drift in (79.11). Determine the condition on \(\lambda\) for negative drift.
5. **A reducible phase example.** Let the phase switching rates be zero. Describe the communicating classes and explain why a single irreducibility-based stability conclusion may fail.
6. **Lean certificate design.** Propose a structure of fields sufficient to check the algebraic part of a QBD stationary-law certificate. Separate properties needed for local balance from those needed for normalization.
7. **Moment formula.** Differentiate \(\Pi(z)\) and derive a formula for the expected level, carefully accounting for the exponent shift.
8. **Order stress test.** Give a pair of noncommuting \(2\times2\) matrices and verify that swapping \(RA_0\) to \(A_0R\) changes the expression. Explain how an M/M/1 specialization can detect orientation mistakes but cannot detect every matrix-order mistake.

## 12. Summary

A QBD process has a countable level coordinate, a finite phase coordinate, and a repeated nearest-neighbor interior generator. With row stationary vectors and source-to-destination blocks, the interior balance recurrence is

\[
\pi_{n-1}A_1+\pi_nA_0+\pi_{n+1}A_{-1}=0.
\]

The matrix-geometric ansatz \(\pi_n=\pi_1R^{n-1}\) reduces this recurrence to the quadratic equation

\[
A_1+RA_0+R^2A_{-1}=0.
\]

The boundary equations determine the initial level vectors. A spectral-radius condition such as \(\rho(R)<1\) makes the tail summable, after which the scalar normalization equation fixes total mass. The formalization benefits from keeping finite block algebra, boundary solving, infinite-series estimates, and countable-state invariance as separate layers.

### Further reading

- M. F. Neuts, *Matrix-Geometric Solutions in Stochastic Models: An Algorithmic Approach*, Johns Hopkins University Press, 1981. The foundational monograph on matrix-geometric methods.
- G. Hanukov and U. Yechiali, “Explicit solutions for continuous-time QBD processes by using relations between matrix geometric analysis and the probability generating functions method,” *Probability in the Engineering and Informational Sciences* 35 (2021), 565–580, [doi:10.1017/S0269964819000470](https://doi.org/10.1017/S0269964819000470). This paper discusses the matrix quadratic and its relation to generating functions.
- V. de Nitto Personè and V. Grassi, “Solution of finite QBD processes,” *Journal of Applied Probability* 33 (1996), 1003–1010, [doi:10.2307/3214981](https://doi.org/10.2307/3214981). This paper gives a matrix-analytic treatment of finite QBD models.
