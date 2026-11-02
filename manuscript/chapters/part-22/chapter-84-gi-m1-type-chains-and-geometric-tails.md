# Chapter 84 — GI/M/1-Type Chains and Geometric Stationary Tails

> **Audience.** This chapter assumes familiarity with QBD and M/G/1-type chains, stationary block vectors, matrix powers, and basic queueing models. It develops the dual skip-free geometry and the matrix-geometric representation associated with arrival-epoch queues.

An M/G/1-type chain can move down by at most one level and may move upward by an arbitrary amount. Its dual, a GI/M/1-type chain, can move upward by at most one and may jump down by an arbitrary amount. The distinction changes the shape of the transition matrix and the stationary recurrence. In the GI/M/1 case, the recurrence suggests a geometric ansatz: stationary level vectors often have the form \(\pi_n=\pi_0R^n\).

This chapter derives that ansatz from the transition blocks, works through scalar queue examples, and shows how a Lean development can keep finite-level balance separate from infinite matrix series and recurrence claims.

## Learning objectives

After this chapter, you should be able to:

- define a block GI/M/1-type chain using a consistent increment convention;
- derive its boundary and interior stationary equations;
- obtain the nonlinear rate-matrix equation from a geometric stationary ansatz;
- distinguish local balance from normalization and positive recurrence;
- derive the scalar rate equation for a GI/M/1 queue;
- organize the transition geometry and infinite sums in Lean-friendly interfaces.

## 1. Skip-free upward transition geometry

Let \(\mathrm{Phase}\) be a finite set. Each level \(n\in\mathbb N\) contains one copy of this phase space. A positive level can move upward by at most one, but it may move down by any number of levels. We use the following increment convention:

- \(A_k\) is the phase transition block for a change of level by \(k\), where \(k\leq 1\);
- \(B_{-i}\) is the block for a transition from positive level \(i\) to the boundary level zero;
- \(B_0\) is the boundary-to-boundary block.

All blocks have source phases in rows and destination phases in columns. The boundary row can move to level one through \(A_1\), but it cannot move above level one. The block transition matrix is

~~~text
               level 0       level 1       level 2       level 3       level 4   ...
level 0          B0             A1
level 1         B-1             A0             A1
level 2         B-2            A-1             A0             A1
level 3         B-3            A-2            A-1             A0             A1
level 4         B-4            A-3            A-2            A-1             A0       A1
  ...
~~~

For example, the transition from level \(i\geq1\) to a positive target \(j\) uses \(A_{j-i}\), provided \(j\leq i+1\). The target-zero block is written separately because many models collapse every sufficiently large downward jump into the same boundary destination. This boundary block need not equal the corresponding interior increment block.

For nonnegative blocks, row stochasticity is expressed by

\[
(B_0+A_1)\mathbf 1=\mathbf 1
\tag{84.1}
\]

at level zero, and, for every \(i\geq1\),

\[
\left(B_{-i}+\sum_{k=1-i}^{1}A_k\right)\mathbf 1=\mathbf 1.
\tag{84.2}
\]

The finite sum in (84.2) includes every positive target level \(1,\ldots,i+1\). The remaining probability is the transition to zero through \(B_{-i}\). This decomposition is often preferable to writing an infinite block row: skip-free upward movement means that each level has only finitely many possible positive targets.

### The level geometry

The row at level \(i\) has the pattern

~~~text
level i  -- B_-i -->  level 0
         -- A_(1-i) -> level 1
         -- A_(2-i) -> level 2
                     ...
         -- A_0 ----> level i
         -- A_1 ----> level i+1
~~~

The increment labels increase with the target. This is an easy place to reverse an index. Always derive the target block from \(k=j-i\), where \(i\) is the source and \(j\) the target.

## 2. Stationary balance by target level

Let \(\pi_n\) be the stationary row vector over phases at level \(n\). A stationary distribution satisfies \(\pi P=\pi\). Target level zero receives mass from the boundary and from every positive level:

\[
\pi_0=\pi_0B_0+\sum_{i=1}^{\infty}\pi_iB_{-i}.
\tag{84.3}
\]

Target level one receives mass from level zero through \(A_1\), and from all positive levels \(i\geq1\) through the block \(A_{1-i}\):

\[
\pi_1=\pi_0A_1+\sum_{i=1}^{\infty}\pi_iA_{1-i}.
\tag{84.4}
\]

For a target level \(n\geq2\), level zero cannot contribute, and a positive source level \(i\) can contribute exactly when \(i\geq n-1\). Hence

\[
\pi_n=\sum_{i=n-1}^{\infty}\pi_iA_{n-i}
=\sum_{j=0}^{\infty}\pi_{n-1+j}A_{1-j}.
\tag{84.5}
\]

The second equality uses \(i=n-1+j\). Checking it at \(j=0\) is useful: the source is level \(n-1\), the target is level \(n\), and the block is \(A_1\), the sole upward transition block.

Unlike the M/G/1-type recurrence in Chapter 83, (84.5) has an infinite sum for each target level. The reason is that a source arbitrarily far above \(n\) can jump down to \(n\). A formalization must therefore state summability or work with a finite-support model before taking a limit.

## 3. The matrix-geometric ansatz

Suppose that for some nonnegative square matrix \(R\), the stationary level vectors have the form

\[
\pi_n=\pi_0R^n,\qquad n\geq0.
\tag{84.6}
\]

Substitute this into (84.5):

\[
\pi_0R^n
=\sum_{j=0}^{\infty}\pi_0R^{n-1+j}A_{1-j}
=\pi_0R^{n-1}\left(\sum_{j=0}^{\infty}R^jA_{1-j}\right).
\tag{84.7}
\]

The multiplication order matters. The stationary vectors are row vectors, so each block occurs on the right; the common factor \(R^{n-1}\) is on the left of the series. This motivates the rate-matrix equation

\[
R=\sum_{j=0}^{\infty}R^jA_{1-j}
=A_1+RA_0+R^2A_{-1}+R^3A_{-2}+\cdots.
\tag{84.8}
\]

If (84.8) holds and the series converges, then the geometric vectors satisfy every interior equation (84.5). Equation (84.4) follows from the same rate equation after multiplication on the left by \(\pi_0\). What remains is the boundary equation (84.3) and normalization.

When the chain is irreducible and positive recurrent under the standard regularity assumptions, matrix-analytic theory selects a minimal nonnegative solution \(R\) of (84.8) with spectral radius less than one. The boundary vector \(\pi_0\) must satisfy

\[
\pi_0=\pi_0\left(B_0+\sum_{i=1}^{\infty}R^iB_{-i}\right),
\tag{84.9}
\]

and total probability one requires

\[
\pi_0\sum_{n=0}^{\infty}R^n\mathbf1
=\pi_0(I-R)^{-1}\mathbf1=1.
\tag{84.10}
\]

The inverse identity in (84.10) is justified by \(\rho(R)<1\), which gives convergence of the matrix Neumann series. The rate equation alone does not establish that the chain is positive recurrent, that the boundary equation has a probability solution, or that the resulting vector is unique. Those are separate hypotheses and conclusions.

### When cancellation is not legitimate

Equation (84.7) is an identity of row vectors. It does not permit cancellation of \(\pi_0R^{n-1}\) to prove that \(R\) must satisfy (84.8): that factor may be singular or have a nontrivial kernel. The rate equation is a sufficient algebraic condition for the geometric ansatz. The theorem that the stationary distribution has this form, and that the relevant rate matrix is minimal, belongs to the matrix-analytic existence theory.

In Lean, this distinction suggests two declarations:

1. an algebraic lemma: a rate equation implies the level recurrence for the proposed geometric vectors;
2. a matrix-analytic theorem: under recurrence and irreducibility hypotheses, the stationary distribution has a rate-matrix representation.

The first can be proved from matrix algebra and a summability hypothesis. The second should depend on a clearly stated theorem or a substantial independent development.

## 4. Worked example: a general-interarrival, exponential-service queue

Consider a single-server queue with independent, identically distributed interarrival times \(A\), and exponential service times of rate \(\mu>0\). Let \(L_n\) be the number of customers in the system immediately before arrival \(n\). The new arrival joins immediately. During the following interarrival interval, let \(N\) count potential service completions. Conditional on \(A\),

\[
N\mid A\sim\operatorname{Poisson}(\mu A).
\]

The next prearrival level is

\[
L_{n+1}=\max(L_n+1-N,0).
\tag{84.11}
\]

At a positive level \(i\), the chain can rise to \(i+1\) only when \(N=0\). It can stay when \(N=1\), and descend by \(k\geq1\) levels when \(N=k+1\), unless the descent reaches zero. Define

\[
p_k=\mathbb P(N=k)
=\mathbb E\!\left[e^{-\mu A}\frac{(\mu A)^k}{k!}\right],
\qquad k\geq0.
\tag{84.12}
\]

Then the scalar interior blocks are

\[
A_1=p_0,\qquad A_0=p_1,\qquad A_{-k}=p_{k+1}\quad(k\geq1).
\tag{84.13}
\]

At level zero, the next level is one exactly when \(N=0\), so \(B_0=1-p_0\) and the upward block remains \(A_1=p_0\). From a positive level \(i\), all events with \(N\geq i+1\) collapse to level zero; consequently

\[
B_{-i}=\mathbb P(N\geq i+1)
=1-\sum_{k=0}^{i}p_k.
\tag{84.14}
\]

Now apply (84.8). Since \(A_{1-j}=p_j\) for all \(j\geq0\), the scalar rate \(r\) satisfies

\[
r=\sum_{j=0}^{\infty}p_jr^j
=\mathbb E[r^N].
\tag{84.15}
\]

Condition on \(A\) and use the probability generating function of a Poisson random variable:

\[
r=\mathbb E\!\left[e^{-\mu A(1-r)}\right]
=\phi_A\!\left(\mu(1-r)\right),
\tag{84.16}
\]

where \(\phi_A(s)=\mathbb E[e^{-sA}]\) is the Laplace transform of the interarrival distribution. The stable rate is the relevant root in \([0,1)\). If \(r<1\), then the geometric level masses normalize as

\[
\pi_n=(1-r)r^n,\qquad n\geq0.
\tag{84.17}
\]

This example shows why the GI/M/1 label is structural: the arrival process is general, while the exponential service law makes the arrival-epoch queue length a Markov chain with skip-free upward transitions. The key balance equation depends on the distribution of the number of potential completions during one interarrival interval.

## 5. Worked example: exponential interarrivals

Take \(A\sim\operatorname{Exp}(\lambda)\). Mixing the conditional Poisson probabilities over \(A\) gives

\[
p_k=\int_0^\infty
\lambda e^{-\lambda t}e^{-\mu t}\frac{(\mu t)^k}{k!}\,dt
=\frac{\lambda\mu^k}{(\lambda+\mu)^{k+1}}.
\tag{84.18}
\]

The probability generating function is

\[
\sum_{k=0}^{\infty}p_kr^k
=\frac{\lambda}{\lambda+\mu(1-r)}.
\tag{84.19}
\]

Thus the rate equation becomes

\[
r=\frac{\lambda}{\lambda+\mu(1-r)}.
\tag{84.20}
\]

After clearing the positive denominator,

\[
\mu r^2-(\lambda+\mu)r+\lambda=0,
\]

whose roots are \(1\) and \(\lambda/\mu\). When \(\lambda<\mu\), the subunit root is \(r=\lambda/\mu\), and

\[
\pi_n=\left(1-\frac{\lambda}{\mu}\right)
\left(\frac{\lambda}{\mu}\right)^n.
\tag{84.21}
\]

This is the familiar stationary distribution of the M/M/1 queue observed immediately before arrivals. The rate-matrix derivation explains how the same geometric structure persists for general interarrival distributions, where the root is determined by the Laplace transform rather than by a simple traffic ratio.

The root \(r=1\) is not the stationary decay rate. It appears because the probability generating function equation always has a stochastic root at one. Selecting the stable root is part of the recurrence and normalization analysis; solving the polynomial equation without checking \([0,1)\) can return the wrong solution.

## 6. Worked example: a finite-support rate equation

Consider a scalar one-phase model with

\[
A_1=0.1,\qquad A_0=0.2,\qquad A_{-1}=0.7,
\]

and \(A_k=0\) for \(k\leq-2\). The positive-level row has interior transition probability \(0.1\) up, \(0.2\) level, and \(0.7\) down one step, except that any transition from level one to or below zero is sent to the boundary. Choose \(B_0=0.9\), \(B_{-1}=0.7\), and \(B_{-i}=0\) for \(i\geq2\). The row sums are correct:

- at level zero, \(B_0+A_1=0.9+0.1=1\);
- at level one, \(B_{-1}+A_0+A_1=0.7+0.2+0.1=1\);
- at level \(i\geq2\), \(A_{-1}+A_0+A_1=0.7+0.2+0.1=1\).

The rate equation is the quadratic

\[
r=0.1+0.2r+0.7r^2.
\tag{84.22}
\]

Its roots are \(1\) and \(1/7\). Choose \(r=1/7\). The boundary equation (84.9) becomes

\[
\pi_0=\pi_0(0.9+0.7r),
\]

which holds because \(0.9+0.7/7=1\). Normalization gives \(\pi_0=1-r=6/7\), and therefore

\[
\pi_n=\frac67\left(\frac17\right)^n.
\tag{84.23}
\]

This small example is useful for proof development. Its rate equation is nonlinear even in one phase, but every sum has finite support, so one can first establish all algebraic identities without analytic machinery.

## 7. A Lean architecture for skip-free structure

### 7.1 Index the blocks by increments

With a finite phase type and real-valued transition probabilities, a basic block type is

~~~lean
abbrev PhaseBlock (Phase : Type) [Fintype Phase] :=
  Matrix Phase Phase ℝ
~~~

Use a function indexed by integer increments for interior blocks. A predicate or support hypothesis records that increments above one vanish. Store the target-zero blocks separately, since the boundary collapse is not generally described by the same increment law.

~~~lean
structure GIBlockData (Phase : Type) [Fintype Phase] where
  A : ℤ → PhaseBlock Phase
  B : ℕ → PhaseBlock Phase
  interior_support : ∀ k, 1 < k → A k = 0
  A_nonneg : ∀ k a b, 0 ≤ A k a b
  B_nonneg : ∀ i a b, 0 ≤ B i a b
  boundary_row_sum :
    (B 0 + A 1) *ᵥ (fun _ : Phase => (1 : ℝ)) = fun _ => 1
  positive_row : ∀ i : ℕ, 0 < i →
    (B i + ∑ k in Finset.Icc (1 - (i : ℤ)) 1, A k) *ᵥ
      (fun _ : Phase => (1 : ℝ)) = fun _ => 1
~~~

This is a Lean-shaped specification, not a ready-made Mathlib structure. The natural-number index \(i\) identifies \(B_i\), the block from level \(i\) to zero; the integer index identifies an interior level increment. In production code, make the phase type and coefficient type explicit, and state matrix nonnegativity separately from the row-sum identities.

The row formula is easiest to implement with a finite interval of integers after proving that the interval bounds are ordered. An alternative is to sum over target levels \(j\in\{1,\ldots,i+1\}\) and use \(A_{j-i}\). The target-index form often produces fewer coercion lemmas because levels already live in \(\mathbb N\).

### 7.2 Define a transition kernel on level-phase pairs

The infinite chain should be represented as a kernel or transition function on \(\mathbb N\times\mathrm{Phase}\). Given source \((i,a)\) and target \((j,b)\):

- if \(j=0\), use the \((a,b)\) entry of \(B_i\);
- if \(j\geq1\) and \(j\leq i+1\), use the \((a,b)\) entry of \(A_{j-i}\);
- otherwise, use zero.

Prove a pointwise row-sum theorem from (84.1)–(84.2), then build the probability kernel from that theorem. Keeping the transition function explicit makes the support arguments available to later proofs: an impossible target is discharged by inequalities, and an allowed target reduces to the matching block entry.

### 7.3 Prove local balance before infinite invariance

For a fixed target level \(n\), derive its balance by partitioning possible source levels. The target-zero proof has all source levels and uses the \(B_i\) blocks. For \(n\geq1\), source levels \(i<n-1\) are impossible by skip-free upward movement; the remaining sources use \(A_{n-i}\). This is a countable sum, so establish the identity under a summability assumption, or first prove it for finitely supported distributions.

A useful separation is:

1. a finite-support lemma, where every sum reduces to a finite sum;
2. a nonnegative-series lemma, which exchanges a sum over source levels with a sum over target phases;
3. an invariance theorem for the full probability measure.

The third step is where Tonelli-style arguments and countable additivity enter. Avoid hiding them inside a broad simplification step. Explicitly expose the nonnegative summands and the index equivalence between target and increment.

### 7.4 State the rate equation with convergence data

For finite phases, define the rate series entrywise or in a matrix norm. A convenient proof interface can package:

- nonnegativity of \(R\) and each \(A_k\);
- convergence of \(\sum_{j\geq0}R^jA_{1-j}\);
- equality of that sum with \(R\);
- convergence of \(\sum_{n\geq0}R^n\);
- the boundary series in (84.9).

Do not define the series using an unproved informal infinite sum and then ask a matrix identity tactic to normalize it. For finite-support blocks, prove the algebraic rate equation first. For infinite support, prove convergence and reindexing as independent lemmas. Spectral-radius hypotheses can later supply convergence, but the API should state the actual summability fact needed by each balance theorem.

There is an additional issue with the word “minimal.” Entrywise order on matrices is useful for stating minimality among nonnegative solutions, but minimality is not an algebraic consequence of the fixed-point equation. It comes from the probabilistic construction or an iteration theorem. Formalize the order statement separately and name the hypotheses that make an iterative construction converge to the least fixed point.

## 8. Common failure modes

1. **Reversing the increment convention.** With \(A_k\) denoting a change \(k\), the block from level \(i\) to level \(j\) is \(A_{j-i}\).
2. **Treating the boundary as an interior row.** Large downward moves from level \(i\) all target zero and are encoded by \(B_i\); they may combine several interior jump probabilities.
3. **Using a finite target sum for interior balance.** A target \(n\) can receive transitions from arbitrarily high source levels, so (84.5) is generally infinite.
4. **Writing the rate equation in the wrong order.** Row-vector balance yields \(R^jA_{1-j}\), not \(A_{1-j}R^j\).
5. **Cancelling a singular row vector.** The geometric ansatz motivates the equation but does not justify cancellation of a potentially singular factor.
6. **Confusing fixed point with recurrence.** A nonnegative solution of the rate equation is not by itself a normalized stationary distribution.
7. **Accepting the root one.** The stochastic root often represents a non-normalizable solution; choose and justify a subunit root.
8. **Using the wrong queue epoch.** Prearrival, postarrival, and arbitrary-time distributions differ. State the observation epoch before deriving the recursion.
9. **Ignoring the boundary-tail probabilities.** In the queue example, \(B_i\) contains \(\mathbb P(N\geq i+1)\), not just one point probability.
10. **Claiming convergence from notation.** Infinite matrix sums require a theorem or an explicit convergence hypothesis.

## 9. Exercises

1. Starting from the block matrix, derive (84.3)–(84.5) and justify every source-level bound.
2. Verify the row sums for the queue blocks in (84.13)–(84.14).
3. Let interarrival times be deterministic with value \(a\). Derive the rate equation \(r=e^{-\mu a(1-r)}\) and discuss why a subunit root is expected when the mean arrival rate is below service capacity.
4. For the finite-support example, derive the two roots of (84.22), check the boundary equation for each, and explain why only one yields a normalized geometric law.
5. Suppose there are two phases and only \(A_1,A_0,A_{-1}\) are nonzero. Write the matrix quadratic rate equation and state which multiplication orders cannot be interchanged.
6. Give a Lean definition of the transition probability on \(\mathbb N\times\mathrm{Phase}\). Prove that a transition from level \(i\) to positive level \(j>i+1\) has probability zero.
7. Prove the interior balance equation for finitely supported level vectors. Identify the exact lemma needed to extend it to summable nonnegative vectors.
8. Separate the claims “\(R\) solves the rate equation,” “\(\rho(R)<1\),” and “\(\pi\) is stationary” into three theorem statements with explicit hypotheses.
9. Derive the exponential-interarrival probabilities (84.18) by integrating the conditional Poisson mass function.
10. Explain why the M/M/1 queue has the same stationary geometric ratio at arrival epochs and in continuous time, while arbitrary-time sampling still requires an observation-epoch argument.

## 10. Summary

A GI/M/1-type chain is skip-free upward and can make arbitrarily large downward jumps. Its positive-level transition blocks are indexed by increments \(k\leq1\), while boundary-hit probabilities require their own blocks \(B_i\). The stationary equations have an infinite source-level sum, and a matrix-geometric ansatz leads to the rate equation

\[
R=A_1+RA_0+R^2A_{-1}+R^3A_{-2}+\cdots.
\]

For a GI/M/1 queue, the scalar rate is the probability generating function of the number of potential service completions during an interarrival interval, evaluated at itself. The Lean development should prove block support and local balance first, then package convergence, minimality, normalization, and positive recurrence as distinct mathematical obligations.

### Further reading

- M. F. Neuts, [“Markov chains with applications in queueing theory, which have a matrix-geometric invariant probability vector”](https://doi.org/10.2307/1426725), *Advances in Applied Probability* 10 (1978), 185–212. The paper establishes matrix-geometric invariant vectors for a class of block-partitioned stochastic matrices and discusses queueing applications.
- G. Latouche and V. Ramaswami, [*Introduction to Matrix Analytic Methods in Stochastic Modeling*](https://doi.org/10.1137/1.9780898719734), SIAM, 1999. The book develops the skip-free matrix paradigms and their computational methods.
