# Chapter 83 — M/G/1-Type Chains and Batch Arrivals

> **Audience.** This chapter assumes familiarity with discrete-time Markov chains, stationary block vectors, generating functions, and QBD processes. It generalizes the QBD structure by allowing a transition to skip arbitrarily many levels upward while remaining skip-free downward.

A QBD changes its level by at most one in either direction. Many queueing models have a different geometry: one service completion can reduce the level by at most one, while a batch arrival can increase it by several customers. Their transition matrices are block upper-Hessenberg rather than block-tridiagonal.

These chains are called M/G/1-type or skip-free to the left. The label describes a matrix structure, not a requirement that every model literally have Poisson arrivals and general service times. This chapter derives the stationary level recurrence and its generating-function equation, then formalizes a bulk-arrival queue as a concrete instance.

## Learning objectives

After this chapter, you should be able to:

- define a block M/G/1-type transition matrix;
- derive the stationary equations for its level vectors;
- turn the level convolution into a matrix generating-function identity;
- distinguish an M/G/1-type tail from a QBD matrix-geometric tail;
- model batch arrivals with finite phase modulation;
- separate local stationary balance from convergence of infinite generating series in Lean.

## 1. Skip-free downward, unrestricted upward

Let the finite phase type be \(\mathrm{Phase}\). At every positive level, a chain may move down by one level, stay in the same level, or move upward by any finite number of levels. Let

- \(A_{-1}\) describe a downward move by one;
- \(A_k\), for \(k\geq0\), describe a move upward by \(k\), including \(k=0\) for staying at the same level.

Each block is a Phase-by-Phase matrix, with source phases in rows and destination phases in columns. The transition matrix has the form

~~~text
             level 0       level 1       level 2       level 3       level 4   ...
level 0        B0            B1            B2            B3            B4
level 1       A-1            A0            A1            A2            A3
level 2         0            A-1           A0            A1            A2
level 3         0              0           A-1           A0            A1
level 4         0              0             0           A-1           A0       A1
  ...
~~~

The boundary row has blocks \(B_j\) because level zero may have different rules and can jump to any level. Above level zero, the repeated block row is shifted down by one position at each level. This is the block upper-Hessenberg structure.

The stochastic row condition for a positive level is

\[
A_{-1}\mathbf1+\sum_{k=0}^{\infty}A_k\mathbf1=\mathbf1,
\tag{83.1}
\]

and at the boundary it is

\[
\sum_{j=0}^{\infty}B_j\mathbf1=\mathbf1.
\tag{83.2}
\]

All blocks have nonnegative entries. These identities say that each row gives total transition probability one after all possible level changes are included. They do not assert that the sum of any individual block row is one.

## 2. Stationary balance by level

Let \(\pi_n\) be the stationary row vector at level \(n\). Since a positive level can only move down by one, level zero receives transitions from level one through \(A_{-1}\), as well as transitions from its own boundary row:

\[
\pi_0=\pi_0B_0+\pi_1A_{-1}.
\tag{83.3}
\]

For a target level \(n\geq1\), there are three sources:

1. level zero, through \(B_n\);
2. level \(n+1\), through a downward step \(A_{-1}\);
3. every level \(n-k\geq1\), through an upward-or-level-preserving block \(A_k\).

Thus

\[
\pi_n=\pi_0B_n+\pi_{n+1}A_{-1}
+\sum_{k=0}^{n-1}\pi_{n-k}A_k,\qquad n\geq1.
\tag{83.4}
\]

The sum is finite for each target level. A source level below zero never appears, and all sources above \(n+1\) are impossible because downward jumps are skip-free.

Equation (83.4) is a convolution in the level index. In a QBD, only three neighboring level vectors interact; here, a target level can receive mass from every lower positive level. This difference changes the stationary solution method. In general, do not impose the QBD ansatz \(\pi_n=\pi_1R^{n-1}\) on an arbitrary M/G/1-type chain. Matrix-analytic solutions use other fundamental matrices and recurrences; the level balance equations themselves remain the safest starting point.

## 3. Generating functions for the stationary tail

For \(|z|<1\), define

\[
\Pi(z)=\sum_{n=1}^{\infty}\pi_nz^n,\qquad
A_+(z)=\sum_{k=0}^{\infty}A_kz^k,\qquad
B_+(z)=\sum_{n=1}^{\infty}B_nz^n.
\tag{83.5}
\]

Assume the series converge absolutely in the chosen region. Multiply (83.4) by \(z^n\) and sum over \(n\geq1\). The source-level sum becomes

\[
\sum_{n=1}^{\infty}\sum_{k=0}^{n-1}\pi_{n-k}A_kz^n
=\Pi(z)A_+(z).
\]

The downward-source term is

\[
\sum_{n=1}^{\infty}\pi_{n+1}A_{-1}z^n
=z^{-1}\bigl(\Pi(z)-\pi_1z\bigr)A_{-1}.
\]

Therefore, for nonzero \(z\) in the convergence region,

\[
\Pi(z)
=\pi_0B_+(z)
+z^{-1}\bigl(\Pi(z)-\pi_1z\bigr)A_{-1}
+\Pi(z)A_+(z).
\tag{83.6}
\]

Multiplying by \(z\) avoids the apparent singularity at zero and yields

\[
\Pi(z)\bigl[zI-A_{-1}-zA_+(z)\bigr]
=z\pi_0B_+(z)-z\pi_1A_{-1}.
\tag{83.7}
\]

Matrix order follows from the row-vector convention: \(\Pi(z)\) is on the left and the transition blocks are on the right. One may be tempted to invert the matrix-valued factor in brackets to “solve” for \(\Pi(z)\). Such an inversion requires a domain where the factor is invertible, and the boundary values at \(z=1\) often require a limiting argument. Keep the identity separate from any analytic continuation or inversion theorem.

### 3.1 The matrix kernel and tail information

The factor in brackets can be written

\[
zI-K(z),\qquad K(z)=A_{-1}+zA_+(z).
\]

The scalar variable \(z\) marks the level increment, while \(K(z)\) packages all interior transition blocks. In the one-phase bulk-arrival example, this reduces to \(z-b(z)\), the denominator in (83.9). In a finite-phase model, zeros of \(\det(zI-K(z))\) can help locate singularities of the stationary generating function and suggest an exponential tail scale.

This spectral reading requires care. A singularity can cancel against the right-hand side of (83.7), repeated roots can introduce polynomial factors in coefficient asymptotics, and a generating function may fail to extend past the unit disk. The block equation is exact in its convergence region; conclusions about asymptotic decay require additional analytic hypotheses. This is another reason not to replace an M/G/1-type stationary law by a guessed geometric sequence.

## 4. Worked example: a single-server bulk-arrival queue

Consider a discrete-time queue with an i.i.d. batch arrival \(B\in\mathbb N\) in each slot. At the start of a slot, if the queue is nonempty, one customer is served; then the batch arrives. If the queue is empty, no service occurs and only the batch arrives. Let \(p_j=\mathbb P(B=j)\) and

\[
b(z)=\sum_{j=0}^{\infty}p_jz^j
\]

be the batch-size probability generating function.

From a positive level \(n\), the next level is \(n-1+B\). Thus the block corresponding to an increment \(k\geq-1\) is \(p_{k+1}\), a scalar. From level zero, the next level is \(B\), so the boundary block \(B_j\) is \(p_j\).

Let \(P(z)=\mathbb E[z^L]\) under a stationary law and let \(\pi_0=\mathbb P(L=0)\). Conditioning on the current level gives

\[
P(z)=\pi_0b(z)+z^{-1}b(z)\bigl(P(z)-\pi_0\bigr).
\tag{83.8}
\]

The first term is the empty queue: only arrivals contribute to the next level. The second term is the nonempty queue: remove one customer for service, then add the batch. Rearranging,

\[
P(z)=\pi_0\,\frac{b(z)(z-1)}{z-b(z)}.
\tag{83.9}
\]

If the batch mean \(\mathbb E[B]=b'(1)\) is less than one, the queue has negative mean drift while busy. Letting \(z\) approach one in (83.9) and using \(P(1)=1\) gives

\[
\pi_0=1-\mathbb E[B].
\tag{83.10}
\]

The formula depends on the entire batch generating function \(b(z)\), not only on its mean. The scalar model is the one-phase version of (83.7), and it makes the service-before-arrival convention explicit. If arrivals occurred before service, the boundary and positive-level transitions would differ.

For a small numerical instance, let \(B=0\) with probability \(4/5\) and \(B=2\) with probability \(1/5\). Then \(\mathbb E[B]=2/5\), so \(\pi_0=3/5\), and \(b(z)=4/5+z^2/5\). Substitution into (83.9) gives

\[
P(z)=\frac{3(4/5+z^2/5)}{4-z}.
\]

At \(z=1\), this equals one. The rational function also displays the distributional tail directly through its pole at \(z=4\). This example is useful for checking signs in the generating-function derivation: reversing service and arrival order would produce a different numerator and boundary probability.

## 5. Worked example: phase-modulated batches with upward skips

Now let the batch distribution depend on a finite environment phase. Suppose there are two phases and the phase transition matrix per slot is

\[
P=\begin{pmatrix}0.8&0.2\\0.1&0.9\end{pmatrix}.
\]

Its stationary row vector is \(\alpha=(1/3,2/3)\). In phase 0, let the batch be zero with probability \(0.9\) and three with probability \(0.1\). In phase 1, let it be zero with probability \(0.6\) and three with probability \(0.4\). Assume that after the batch is drawn, the phase moves according to \(P\), independently conditional on the current phase.

The joint batch-and-next-phase blocks are

\[
C_0=\operatorname{diag}(0.9,0.6)P
=\begin{pmatrix}0.72&0.18\\0.06&0.54\end{pmatrix},
\]

\[
C_3=\operatorname{diag}(0.1,0.4)P
=\begin{pmatrix}0.08&0.02\\0.04&0.36\end{pmatrix}.
\]

They satisfy \(C_0+C_3=P\). When the queue is positive, batch zero produces a net level change of \(-1\), so \(A_{-1}=C_0\). Batch three produces a net change of \(+2\), so \(A_2=C_3\); all other \(A_k\) vanish. At the empty boundary, \(B_0=C_0\) and \(B_3=C_3\).

The stationary mean batch size is

\[
\frac13(0.1\cdot3)+\frac23(0.4\cdot3)=0.9<1.
\]

Under the finite-phase irreducibility assumptions, the negative drift implies positive recurrence. The transition from a positive level can jump upward by two, so this is not a QBD even though there are only two nonzero interior blocks. Here \(A_{-1}=C_0\) and \(A_+(z)=C_3z^2\); the power \(z^2\) records the net upward increment rather than the batch size.

### 5.1 An executable phase-modulated batch certificate

For the two-phase example above, (C_0) and (C_3) are exact joint probabilities for the batch and next phase. The executable certificate checks that they are nonnegative and sum to the phase transition matrix, verifies the stationary phase law, and computes the stationary mean batch size (9/10). It also encodes the level update explicitly: batch zero moves a positive level down by one, while batch three moves it up by two; at the empty boundary, batch three reaches level three.

```lean
abbrev BatchMatrix := Matrix (Fin 2) (Fin 2) ℚ

def batchPhaseKernel : BatchMatrix := !![4 / 5, 1 / 5; 1 / 10, 9 / 10]
def batchPhaseStationary (i : Fin 2) : ℚ := if i = 0 then 1 / 3 else 2 / 3
def batchZeroBlock : BatchMatrix := !![18 / 25, 9 / 50; 3 / 50, 27 / 50]
def batchThreeBlock : BatchMatrix := !![2 / 25, 1 / 50; 1 / 25, 9 / 25]

def batchRowMultiply (p : Fin 2 → ℚ) (A : BatchMatrix) (j : Fin 2) : ℚ :=
  ∑ i : Fin 2, p i * A i j

def conditionalBatchMean (i : Fin 2) : ℚ :=
  3 * ∑ j : Fin 2, batchThreeBlock i j

def stationaryBatchMean : ℚ :=
  ∑ i : Fin 2, batchPhaseStationary i * conditionalBatchMean i

def positiveLevelNext (level batch : Nat) : Nat := level - 1 + batch

theorem batchPhaseStationary_normalized :
    ∑ i : Fin 2, batchPhaseStationary i = 1 := by
  norm_num [batchPhaseStationary]

theorem batchPhaseStationary_invariant :
    ∀ j : Fin 2,
      batchRowMultiply batchPhaseStationary batchPhaseKernel j =
        batchPhaseStationary j := by
  intro j
  fin_cases j <;>
    norm_num [batchRowMultiply, batchPhaseStationary, batchPhaseKernel]

theorem batchPhaseKernel_rows_stochastic (i : Fin 2) :
    ∑ j : Fin 2, batchPhaseKernel i j = 1 := by
  fin_cases i <;> norm_num [batchPhaseKernel]

theorem batch_blocks_decompose_phase_kernel :
    batchZeroBlock + batchThreeBlock = batchPhaseKernel := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [batchZeroBlock, batchThreeBlock, batchPhaseKernel, Matrix.add_apply]

theorem batch_blocks_row_mass_one (i : Fin 2) :
    ∑ j : Fin 2, (batchZeroBlock + batchThreeBlock) i j = 1 := by
  rw [batch_blocks_decompose_phase_kernel]
  exact batchPhaseKernel_rows_stochastic i

theorem batch_blocks_nonnegative :
    (∀ i j : Fin 2, 0 ≤ batchZeroBlock i j) ∧
      (∀ i j : Fin 2, 0 ≤ batchThreeBlock i j) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [batchZeroBlock, batchThreeBlock]

theorem conditional_batch_means :
    (conditionalBatchMean 0 = 3 / 10) ∧
      (conditionalBatchMean 1 = 6 / 5) := by
  norm_num [conditionalBatchMean, batchThreeBlock]

theorem batch_stationary_mean_is_nine_tenths : stationaryBatchMean = 9 / 10 := by
  norm_num [stationaryBatchMean, conditionalBatchMean, batchPhaseStationary,
    batchThreeBlock]

theorem batch_drift_is_negative : stationaryBatchMean < 1 := by
  rw [batch_stationary_mean_is_nine_tenths]
  norm_num

theorem positiveLevel_zero_batch_moves_down (level : Nat) :
    positiveLevelNext level 0 = level - 1 := by
  simp [positiveLevelNext]

theorem positiveLevel_three_batch_skips_up_two (level : Nat) (hlevel : 0 < level) :
    positiveLevelNext level 3 = level + 2 := by
  simp [positiveLevelNext]
  omega

theorem emptyLevel_three_batch_reaches_three : positiveLevelNext 0 3 = 3 := by
  norm_num [positiveLevelNext]
```

The drift inequality is a finite calculation under the given phase-stationary weights. As in Section 5, concluding positive recurrence for the full chain additionally uses the stated finite-phase irreducibility assumptions; the code does not formalize that infinite-state theorem.

## 6. From transition blocks to a formal proof

The local stationary recurrence is a finite sum at each target level. This is an excellent first theorem in Lean: it avoids analytic convergence and only requires unfolding the block structure of the transition matrix. A proof can be organized as:

1. split the stationary equation at target level zero and positive target levels;
2. use the block sparsity to identify the only possible source levels;
3. rewrite each source-to-target block in terms of \(A_{-1}\), \(A_k\), or \(B_n\);
4. collect the finitely many contributions to obtain (83.3) and (83.4).

Represent the upward blocks as a function \(\mathbb N\to\mathrm{Matrix}\ \mathrm{Phase}\ \mathrm{Phase}\ \mathbb R\), alongside a separate downward block. At level \(n\), only the indices \(0,\ldots,n-1\) enter the balance equation, so this local theorem does not need a summability assumption over all upward blocks.

The generating-function theorem has additional hypotheses. To exchange the double sum in (83.6), prove absolute convergence or work in formal power series with coefficientwise finiteness. The boundary series and upward-block series need their own convergence statements. For \(|z|<1\), nonnegative stochastic rows often provide useful majorants, but the proof must still establish the relevant bound.

Keep the analytic generating function separate from a formal power series if the library's convergence interfaces make the former cumbersome. First prove the coefficient identity in the formal series ring; then prove that evaluation at a real or complex \(z\) is valid inside the convergence radius. This two-stage design preserves the combinatorial proof even if the analytic estimates change.

For a probability measure on the full state space, local balance is not the entire argument. One must also show that the block rows define a stochastic kernel, the level masses are nonnegative and sum to one, and the local equations imply invariance against the infinite transition matrix. Nonnegative series help exchange sums, but that interchange should be an explicit theorem. A useful library boundary is a lemma that takes level vectors satisfying (83.3)–(83.4), together with total mass one, and returns stationarity of the induced measure.

The order of factors is also visible in the formulation. The stationary block \(\pi_i\) is a row vector, so each probability block is on the right. Matrix blocks with different source and target phase types should retain those types rather than being coerced to square matrices. The level recurrence is a convolution and a useful test of finite sums over source levels and dependent matrix dimensions.

## 7. What the M/G/1 label does and does not mean

The name comes from classical queues with Markovian arrivals, general service, and one server. In matrix-analytic work, it identifies a block-Hessenberg transition structure: one-step downward movement and potentially many-step upward movement. A batch-arrival model with deterministic service can be M/G/1-type in this structural sense.

The dual G/M/1-type structure is skip-free upward and may skip downward. A QBD is the intersection where both directions move by at most one level. These classes suggest different solution tools:

- QBDs lead naturally to one quadratic matrix equation and a matrix-geometric tail;
- M/G/1-type chains lead to a convolutional level recurrence and generating-function or fundamental-matrix methods;
- G/M/1-type chains have a dual structure with a different matrix-geometric orientation.

The formalization should state the transition geometry explicitly. A theorem proved for a block tridiagonal generator should not be silently applied to a block upper-Hessenberg transition matrix.

## 8. Common failure modes

1. **Allowing arbitrary downward jumps.** M/G/1-type means downward changes are at most one; larger upward jumps are the unrestricted direction.
2. **Dropping the boundary blocks.** Level zero may have a distinct jump distribution and contributes \(\pi_0B_n\) to every positive target level.
3. **Summing the wrong sources.** Target \(n\) receives from levels \(1,\ldots,n\) through \(A_0,\ldots,A_{n-1}\), plus level \(n+1\) through \(A_{-1}\).
4. **Using the QBD geometric ansatz without proof.** The M/G/1-type recurrence is a convolution and generally does not reduce to one rate matrix power.
5. **Inverting a generating-function matrix at a singular point.** The factor in (83.7) can be singular at \(z=1\); normalization may require a limit.
6. **Interchanging infinite sums without convergence.** The formal coefficient identity and its analytic evaluation are separate results.
7. **Confusing batch size with net level increment.** With one service completion before arrivals, a batch of three raises a positive queue by two.
8. **Forgetting slot order at the boundary.** An empty queue receives the batch without first serving a nonexistent customer.

## 9. Exercises

1. **Derive the level recurrence.** Starting from the block-Hessenberg matrix, identify every source of target level \(n\) and prove (83.4).
2. **Generate the scalar queue law.** Starting from the service-before-arrival dynamics, derive (83.8) and solve for \(P(z)\).
3. **Normalize at one.** Use \(b(1)=1\) and \(b'(1)=\mathbb E[B]<1\) to derive \(\pi_0=1-\mathbb E[B]\) from (83.9).
4. **Change slot order.** Suppose batch arrivals occur before service. Derive the transition from a positive level and describe the changed boundary behavior.
5. **Check the two-phase model.** Verify that \(C_0+C_3=P\), compute the stationary mean batch size, and list all nonzero M/G/1-type blocks.
6. **Formal-series proof.** Show coefficientwise that the double sum in (83.6) equals \(\Pi(z)A_+(z)\).
7. **QBD special case.** Restrict batches to sizes zero, one, or two. Identify when the positive-level structure is tridiagonal and write the corresponding QBD blocks.
8. **Lean abstraction.** Propose the fields for a block M/G/1-type chain, separating stochastic row sums, skip-free structure, stationary balance, and analytic convergence.

## 10. Summary

An M/G/1-type chain is skip-free downward and may jump arbitrarily far upward. Its block transition matrix is upper-Hessenberg, with a separate boundary row. The stationary probability at a target level satisfies the finite convolution equation (83.4). Summing those equations produces the matrix generating-function identity (83.7), provided the relevant series converge.

Bulk-arrival queues illustrate the structure directly: a positive queue loses one customer to service and then gains a batch, while an empty queue only gains the batch. Their stationary generating functions depend on the full batch law. The Lean development should first prove local balance from block sparsity, then handle analytic convergence as a separate layer.

### Further reading

- G. Latouche and V. Ramaswami, [“Processes, Skip-Free in One Direction,” Chapter 13 of *Introduction to Matrix Analytic Methods in Stochastic Modeling*](https://doi.org/10.1137/1.9780898719734.ch13), ASA-SIAM Series on Statistics and Applied Probability, 1999. This chapter introduces the block-Hessenberg M/G/1-type structure and queueing examples with batch arrivals.
- M. F. Neuts, *Matrix-Geometric Solutions in Stochastic Models: An Algorithmic Approach*, Johns Hopkins University Press, 1981. A foundational source on matrix-analytic methods for structured stochastic models.
