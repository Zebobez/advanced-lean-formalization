# Chapter 81 — Markovian Arrival Processes and MAP/M/1 Queues

> **Audience.** This chapter assumes familiarity with finite-state continuous-time Markov chains, QBD processes, and matrix-geometric stationary distributions. It replaces the Poisson arrival assumption with a finite-state Markovian arrival process and shows how to preserve a QBD representation.

A Poisson process has independent exponential gaps and a constant arrival rate. Many workloads are not that regular: arrivals cluster, quiet periods alternate with bursts, and the chance of a new arrival depends on a latent operating mode. A Markovian arrival process (MAP) represents such behavior by coupling arrival events to a finite-state continuous-time Markov chain.

The central modeling benefit is that the joint state “number in the queue, arrival phase” is still a continuous-time Markov chain with a repeated block structure. A MAP/M/1 queue therefore fits directly into the QBD framework of Chapters 79 and 80. The formalization challenge is to keep the phase evolution, arrival count, and queue level distinct while checking that their blocks assemble into one valid generator.

## Learning objectives

After this chapter, you should be able to:

- define a MAP by its no-arrival and arrival rate matrices;
- derive its stationary mean arrival rate from the phase stationary distribution;
- write the generator blocks for a MAP/M/1 queue;
- derive the QBD matrix quadratic and the load condition;
- distinguish a MAP from a Poisson process and avoid an unjustified PASTA argument;
- organize a Lean development around the arrival matrices and QBD certificate.

## 1. Two matrices encode the arrival mechanism

Let the finite type Phase record the background state. A MAP is described by two matrices \(D_0\) and \(D_1\):

- \(D_0(i,j)\) gives the rate of a phase transition from \(i\) to \(j\) with no arrival;
- \(D_1(i,j)\) gives the rate of an event that produces one arrival and leaves the phase at \(j\), given that it was \(i\) just before the event.

The matrix \(D_1\) is entrywise nonnegative. Off-diagonal entries of \(D_0\) are nonnegative, while its diagonal entries account for all events leaving a phase, including arrivals. The matrix

\[
D=D_0+D_1
\tag{81.1}
\]

is the generator of the background phase process after arrival events are not marked. Thus \(D\mathbf 1=0\). The matrix \(D_0\) by itself generally does not have row sums zero.

The combined count-and-phase process has state \((n,i)\), where \(n\) is the number of arrivals observed and \(i\) is the phase. Its generator has \(D_0\) on the level-preserving diagonal and \(D_1\) on the block that increments the count:

~~~text
count 0       D0       D1        0        0       ...
count 1        0       D0       D1        0       ...
count 2        0        0       D0       D1       ...
  ...
~~~

This diagram is a bookkeeping view. It says that a \(D_1\) event increments the count by exactly one; a batch-arrival model would require more marked blocks.

The probability generating matrix for the count over an interval of length \(t\) is built from

\[
D(z)=D_0+zD_1.
\tag{81.2}
\]

If the initial phase distribution is a row vector \(\gamma\), then the generating function of the arrival count, with the final phase summed out, is

\[
\mathbb E_\gamma[z^{N(t)}]=\gamma e^{D(z)t}\mathbf 1.
\tag{81.3}
\]

At \(z=1\), this reduces to \(\gamma e^{Dt}\mathbf 1=1\), as required for a probability generating function. Differentiation at \(z=1\) recovers expected arrival counts.

## 2. The long-run arrival rate

Assume the phase generator \(D\) is irreducible, and let \(\alpha\) be its stationary row distribution:

\[
\alpha D=0,\qquad \alpha\mathbf 1=1.
\]

In phase \(i\), the instantaneous arrival rate is the \(i\)-th component of \(D_1\mathbf 1\). Averaging these phase-dependent rates against \(\alpha\) gives the long-run mean arrival rate

\[
\lambda=\alpha D_1\mathbf 1.
\tag{81.4}
\]

This formula counts arrivals even when an arrival event changes the phase. A diagonal entry of \(D_1\) also represents a genuine arrival; the phase stays the same, but the arrival count increases.

The arrival rate is not enough to characterize the process. Two MAPs can have the same value of \(\lambda\) but different correlations and different queue-length distributions. The finite background phase retains this temporal structure. In particular, replacing a MAP by a Poisson process with the same mean rate can change tail probabilities substantially.

### 2.1 Variability in a Markov-modulated Poisson process

For an MMPP, write the phase-dependent arrival-rate column as

\[
\ell=(\lambda_0,\ldots,\lambda_{m-1})^{\mathsf T},
\]

and let \(S\) have stationary row vector \(\alpha\). Conditional on the entire phase path, arrivals form an inhomogeneous Poisson process with random integrated intensity

\[
\Lambda_t=\int_0^t \lambda_{J_s}\,ds.
\]

The conditional mean and variance of \(N(t)\) both equal \(\Lambda_t\). The law of total variance therefore gives

\[
\operatorname{Var}(N(t))
=\mathbb E[\Lambda_t]+\operatorname{Var}(\Lambda_t).
\]

When the phase begins in stationarity, its intensity covariance at lag \(s\) is

\[
C(s)=\alpha\,\operatorname{diag}(\ell)e^{Ss}\ell-(\alpha\ell)^2.
\]

Consequently,

\[
\operatorname{Var}(N(t))
=\lambda t+2\int_0^t(t-s)C(s)\,ds,
\qquad \lambda=\alpha\ell.
\tag{81.5}
\]

The first term is Poisson variation at the mean rate. The integral records extra variation created by the persistent environment. If high-arrival phases tend to last for a long time, their positive intensity covariance contributes a larger count variance over a long observation window. This is one mathematical reason an average-rate replacement can understate queueing risk.

For a Lean proof, isolate the probability identity \(\operatorname{Var}(N)=\mathbb E[\operatorname{Var}(N\mid J)]+\operatorname{Var}(\mathbb E[N\mid J])\) from the finite-state semigroup calculation of \(C(s)\). Then the queue model can consume a proved arrival-rate and variability interface without reopening the pathwise conditional-Poisson argument.

## 3. The MAP/M/1 state and generator

Consider a single-server queue with infinite waiting space. Arrivals follow a MAP \((D_0,D_1)\); service times are exponential with rate \(\mu>0\), independent of the arrival phase and arrival process. The state is

\[
(L_t,J_t)\in\mathbb N\times\mathrm{Phase},
\]

where \(L_t\) is the number of customers in the system and \(J_t\) is the MAP phase. Because service is exponential, no extra service-age coordinate is needed.

At level zero, service cannot complete. The boundary blocks are

\[
B_{00}=D_0,\qquad B_{01}=D_1.
\]

At every positive level, an arrival increases the level, a service completion decreases it by one without changing the MAP phase, and a no-arrival phase transition leaves the level unchanged. In the row-generator convention of Chapter 79, the repeated blocks are

\[
A_1=D_1,\qquad A_0=D_0-\mu I,\qquad A_{-1}=\mu I.
\tag{81.6}
\]

The resulting generator has the form

~~~text
               level 0       level 1       level 2       level 3      ...
level 0          D0             D1             0             0
level 1           μI         D0 - μI           D1            0
level 2            0             μI         D0 - μI          D1
level 3            0              0            μI          D0 - μI      D1
  ...
~~~

Every full row sums to zero. At level zero, \(D_0\mathbf 1+D_1\mathbf 1=0\). At a positive level,

\[
\mu I\mathbf 1+(D_0-\mu I)\mathbf 1+D_1\mathbf 1
=D_0\mathbf 1+D_1\mathbf 1=0.
\]

Off-diagonal rates are nonnegative because \(D_0\) has nonnegative off-diagonal entries, \(D_1\geq0\), and the service block \(\mu I\) connects distinct levels. The diagonal subtraction \(-\mu I\) accounts for service completions in the within-level block.

## 4. Stability and the rate-matrix equation

The mean upward level drift under the stationary phase distribution is the mean arrival rate minus the service rate:

\[
\alpha(D_1-\mu I)\mathbf 1=\lambda-\mu.
\tag{81.7}
\]

For an irreducible MAP/M/1 queue with finite background phase and the usual non-explosion assumptions, the stability condition is

\[
\lambda<\mu.
\tag{81.8}
\]

The traffic intensity \(\rho=\lambda/\mu\) describes offered load, but it does not determine the full stationary law when arrivals are correlated. Chapter 79’s matrix-geometric method gives level vectors \(\pi_n=\pi_1R^{n-1}\) for \(n\geq1\). Substituting (81.6) into its matrix quadratic gives

\[
D_1+R(D_0-\mu I)+\mu R^2=0.
\tag{81.9}
\]

The boundary equations are

\[
\pi_0D_0+\pi_1\mu I=0,
\tag{81.10}
\]

\[
\pi_0D_1+\pi_1(D_0-\mu I)+\pi_2\mu I=0,
\tag{81.11}
\]

with \(\pi_2=\pi_1R\). The normalization equation is the QBD equation from Chapter 79:

\[
\pi_0\mathbf 1+\pi_1(I-R)^{-1}\mathbf 1=1,
\tag{81.12}
\]

when \(\rho(R)<1\). The arrival model changes the three interior blocks, while the solution strategy remains the same.

## 5. Worked example: a two-state modulated Poisson process

A Markov-modulated Poisson process (MMPP) is a special MAP. The background switches between states 0 and 1 at rates \(a\) and \(b\), and the arrival rate is \(\lambda_0\) or \(\lambda_1\) according to the current state:

\[
S=\begin{pmatrix}-a&a\\b&-b\end{pmatrix},\qquad
D_1=\begin{pmatrix}\lambda_0&0\\0&\lambda_1\end{pmatrix},\qquad
D_0=S-D_1.
\]

Here \(D=D_0+D_1=S\), whose stationary row vector is

\[
\alpha=\left(\frac{b}{a+b},\frac{a}{a+b}\right).
\]

The effective arrival rate is

\[
\lambda=\frac{b\lambda_0+a\lambda_1}{a+b}.
\]

For example, set \(a=1\), \(b=2\), \(\lambda_0=1/2\), and \(\lambda_1=2\). Then \(\alpha=(2/3,1/3)\) and \(\lambda=1\). If \(\mu=3/2\), the offered load is \(2/3\), so the queue is stable under (81.8). The matrices are

\[
D_0=\begin{pmatrix}-3/2&1\\2&-4\end{pmatrix},\qquad
D_1=\begin{pmatrix}1/2&0\\0&2\end{pmatrix}.
\]

The positive-level blocks follow from (81.6), and \(R\) solves (81.9). The arrivals cluster during phase 1 and become sparse during phase 0, despite having the same mean rate as a Poisson process of rate one. A scalar M/M/1 calculation using only \(\rho=2/3\) would discard that burst structure.

## 6. Worked example: a Poisson stream with an independent phase

Take a finite-state environment with generator \(S\), and let arrivals form a Poisson process of rate \(\lambda\), independent of that environment. A MAP representation is

\[
D_1=\lambda I,\qquad D_0=S-\lambda I.
\]

Then \(D=D_0+D_1=S\), so the environment continues to evolve independently of arrivals. The queue length is the ordinary M/M/1 queue and has stationary marginal

\[
\mathbb P(L=n)=(1-\rho)\rho^n,\qquad \rho=\lambda/\mu<1.
\]

At an arbitrary stationary time, the joint law factors into this geometric queue-length law and the stationary environment distribution of \(S\), because the queue dynamics do not depend on that environment.

This is a useful special case, but it does not mean the matrix rate factor in every representation must equal \(\rho I\). The vector recurrence can hold after multiplication by a particular stationary phase row vector even when a full matrix polynomial identity does not hold for that scalar guess. Chapter 79 emphasized this distinction: the matrix equation is a stronger, phase-uniform certificate.

## 7. Arrival observations and the PASTA boundary

Poisson Arrivals See Time Averages (PASTA) is specific to Poisson sampling under its standard independence conditions. A general MAP is not Poisson: its event rate depends on the current phase, and arrival events may themselves change that phase. Therefore the phase distribution observed by arrivals can differ from the stationary phase distribution \(\alpha\) observed at an arbitrary time.

For example, in an MMPP the phase-\(i\) arrival intensity is \(\lambda_i\), so phases with larger \(\lambda_i\) are overrepresented at arrival epochs. Queue length and phase are also generally dependent in steady state, so an arrival-epoch queue distribution should be derived from an arrival/Palm calculation or the appropriate transition blocks, not copied from the time-stationary distribution.

The modeling distinction matters in performance analysis. Waiting time for a typical arrival, queue length at a typical time, and the environment at a typical departure are different sampling schemes. A formal proof should attach each expectation to the correct probability law.

## 8. Lean formalization plan

The MAP blocks are finite matrices and the queue level is countable. A development can reuse the QBD definitions from Chapters 79–80 and provide a MAP-specific constructor for the block data.

### 8.1 Arrival-process invariants

Record that \(D_1\) is entrywise nonnegative, the off-diagonal entries of \(D_0\) are nonnegative, and \(D_0+D_1\) has zero row sums. If irreducibility is required for the stationary phase law, keep it as a separate hypothesis. Prove the row-rate vector \(D_1\mathbf 1\) is nonnegative and derive the scalar mean rate \(\lambda=\alpha D_1\mathbf 1\).

### 8.2 Queue-generator assembly

Define the boundary and interior blocks explicitly from \(D_0,D_1,\mu\). A block-row lemma should show that their row sums add to zero at level zero and every positive level. Separate off-diagonal nonnegativity from row-sum zero; together they establish the generator conditions.

### 8.3 Reuse the QBD stationary certificate

Once the MAP queue has been shown to be a QBD, reuse the rate-matrix equation, boundary equations, and normalization theorem. The MAP-specific proof should establish the substitution from (81.6) into the generic QBD theorem, rather than reproving matrix-geometric convergence.

### 8.4 Keep arrival observations separate

If the theorem concerns a typical arrival, encode its arrival-epoch law explicitly. Do not obtain it by silently reusing the time-stationary measure. This distinction is also a useful type-design principle: different sampling schemes should have distinct definitions even when they share the same underlying state space.

## 9. Common failure modes

1. **Treating \(D_0\) as a generator.** It includes the loss of mass caused by arrivals; only \(D_0+D_1\) is the background generator.
2. **Dropping diagonal entries of \(D_1\).** A phase-preserving arrival still increments the queue level.
3. **Forgetting that \(D_1\) may change phase.** Arrival blocks are matrices, not necessarily diagonal rate vectors.
4. **Using the mean arrival rate as a complete model.** Equal mean rates do not imply equal correlation or queue tails.
5. **Adding service transitions at level zero.** An empty queue has no service completion.
6. **Applying the scalar M/M/1 stationary law to a modulated MAP.** The load ratio alone does not determine the MAP/M/1 distribution.
7. **Invoking PASTA for a general MAP.** Arrival-epoch observations require their own law.
8. **Mixing the arrival count with the queue level.** The count process records cumulative input; the queue level also subtracts service completions.

## 10. Exercises

1. **Check the MAP generator.** From the definitions of \(D_0\) and \(D_1\), prove that the row sums of \(D=D_0+D_1\) vanish.
2. **Derive the mean rate.** In phase \(i\), the arrival intensity is \((D_1\mathbf 1)_i\). Average this quantity under \(\alpha\) to obtain (81.4).
3. **Verify queue rows.** Check the row-sum identity at level zero and at a positive level using (81.6).
4. **Compute an MMPP rate.** Let \(a=3\), \(b=1\), \(\lambda_0=1/4\), and \(\lambda_1=5/4\). Find the stationary phase distribution, mean arrival rate, and service rates that satisfy the strict stability condition.
5. **Poisson special case.** Show that \(D_1=\lambda I\) and \(D_0=S-\lambda I\) encode a Poisson arrival stream independent of the phase chain generated by \(S\).
6. **Arrival bias.** For the two-state MMPP, compare the stationary phase weights with the phase weights seen immediately before an arrival. Identify when the two distributions agree.
7. **Lean interfaces.** Design separate structures for MAP validity, a MAP/M/1 QBD block system, and an arrival-epoch expectation. Explain which proofs each structure should own.
8. **Model comparison.** Construct two MMPPs with the same mean rate but different phase switching speeds. Explain why their modulated arrival counts need not have the same variance over a fixed interval.

## 11. Summary

A MAP uses \(D_0\) for no-arrival transitions and \(D_1\) for one-arrival transitions, with \(D_0+D_1\) the phase generator. If \(\alpha\) is its stationary distribution, the mean arrival rate is \(\lambda=\alpha D_1\mathbf 1\). A MAP/M/1 queue is a QBD with blocks \(D_1\), \(D_0-\mu I\), and \(\mu I\); its stability condition is \(\lambda<\mu\), and its rate matrix solves the corresponding quadratic.

The model preserves the finite-matrix advantage of Poisson queues while representing dependence and bursts. Formalization should keep the marked arrival events, unmarked phase changes, service transitions, and sampling law explicit, then reuse the generic QBD stationary theorem.

### Further reading

- M. F. Neuts, “A versatile Markovian point process,” *Journal of Applied Probability* 16 (1979), 764–779, [doi:10.2307/3213143](https://doi.org/10.2307/3213143). This foundational paper develops the finite-state point-process model that includes MAP and Markov-modulated Poisson examples.
- V. Subramanian and R. Srikant, [“Tail probabilities in priority queues”](https://www.hamilton.ie/vsubramanian/questapaper2000.pdf), *Queueing Systems* 34 (2000), 215–236. Its opening section states the MAP phase generator and mean-rate formula \(\lambda=\alpha D_1\mathbf 1\).
- G. Latouche and V. Ramaswami, [*Introduction to Matrix Analytic Methods in Stochastic Modeling*](https://epubs.siam.org/doi/book/10.1137/1.9780898719734), ASA-SIAM Series on Statistics and Applied Probability, 1999. Chapters on phase-type processes and homogeneous QBDs provide the broader matrix-analytic framework.
