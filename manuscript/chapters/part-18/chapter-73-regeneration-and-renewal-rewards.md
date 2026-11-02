# Chapter 73 — Regeneration and Renewal Rewards

> **Audience.** This chapter assumes finite continuous-time chains, the strong Markov property, return times, and the Green kernels from Chapter 72. It derives stationary laws and long-run averages by decomposing paths into independent return cycles.

Stationarity is usually introduced through the equation πQ=0. A different construction observes the chain whenever it returns to a chosen state. Between successive returns, the path is a regenerative cycle: after each return, the future restarts with the same law and is independent of the past. Expected occupation in one cycle, divided by expected cycle length, gives the stationary distribution. The same decomposition proves a renewal-reward theorem for time averages.

This approach is useful when a model has a natural regeneration state, such as an empty queue or a reset configuration. It also provides a probabilistic interpretation of stationary weights that complements the tree formula and linear-response methods.

## Learning objectives

By the end of the chapter, you should be able to:

- define a return cycle for a finite irreducible continuous-time chain;
- prove successive cycles are independent and identically distributed;
- construct the stationary law from expected occupation per cycle;
- express excursion occupation using a killed Green kernel;
- derive the renewal-reward limit for bounded state observables;
- formalize unbounded return times through truncation and integrability.

## 1. Regeneration at a state

Let X_t be an irreducible continuous-time Markov chain on a finite state space S, and fix a reference state a. Assume |S|>1 so the exit rate
\[
  q_a=\sum_{j\ne a}q(a,j)
\]
is positive. Start the chain at a. Define the departure time
\[
  D=\inf\{t>0:X_t\ne a\},
\]
and the cycle return time
\[
  C=\inf\{t\geq D:X_t=a\}.
\]
The cycle includes the initial holding time at a, the excursion away from a, and the jump back to a. It ends at the first return after departure, so (C>0) almost surely.

At time C, the process is again at a. The strong Markov property implies that the process after C is independent of the history up to C and has the same law as a fresh process started at a. Repeating the construction gives cycle lengths (C_1,C_2,\ldots) and path segments that are independent and identically distributed.

Finiteness of S and irreducibility imply finite moments for C. One way to prove this is to find a time T>0 and ε>0 such that, from every state other than a, the probability of hitting a within time T is at least ε. A finite path of positive-rate transitions gives positive probability; taking a minimum over finitely many states yields a uniform bound. Iterating by the Markov property gives a geometric tail for the return time. The initial holding at a is exponential with positive rate, so it also has finite moments.

## 2. Expected occupation in one cycle

For an observable f:S→ℝ, define its cycle reward and cycle length by
\[
  R_f=\int_0^C f(X_t)\,dt,\qquad C.
\]
Since f is bounded and \(\mathbb E_a[C]<\infty\), the expected reward is finite. Define the unnormalized occupation vector
\[
  m(i)=\mathbb E_a\left[\int_0^C\mathbf1_{\{X_t=i\}}\,dt\right].
\]
Then \(m(f)=\sum_i m(i)f(i)=\mathbb E_a[R_f]\), and \(\sum_i m(i)=\mathbb E_a[C]\).

The normalized vector
\[
  \pi(i)=\frac{m(i)}{\mathbb E_a[C]}
\]
is a probability distribution. The key theorem is that it is stationary for Q. This establishes existence without first solving πQ=0; uniqueness for the finite irreducible chain then identifies it with the usual stationary law.

## 3. Why cycle occupation is stationary

For any f, Dynkin’s formula stopped at C gives
\[
  \mathbb E_a[f(X_C)-f(X_0)]
      =\mathbb E_a\left[\int_0^C Qf(X_t)\,dt\right].
\]
The left side is zero because (X_0=X_C=a). Therefore
\[
  m(Qf)=0\quad\text{for every }f,
\]
which is the row-vector equation mQ=0. Dividing by \(\mathbb E_a[C]\) proves πQ=0.

The stopping time C is not bounded, so apply Dynkin’s formula first at \(C\wedge T\). The generator \(Qf\) is bounded on the finite state space, and \(\mathbb E_a[C]<\infty\), hence the drift integral converges in L¹ as T→∞. The terminal term converges by bounded convergence because \(X_{C\wedge T}\to X_C\) almost surely. This is the point at which finite expected return time is needed; optional stopping at C without an integrability argument is incomplete.

There is a purely algebraic alternative. The transition law from a to a after one cycle is the point mass at a, and the expected accumulated generator drift over the cycle vanishes by the martingale property. The probabilistic and algebraic statements should share the same occupation vector definition so the proof does not duplicate indexing work.

## 4. Worked example: a two-state chain

Let (0\to1) have rate a and (1\to0) have rate b, with a,b>0. Regenerate at state 0. A cycle consists of an exponential holding time at 0 with mean 1/a, followed by an exponential holding time at 1 with mean 1/b, after which the process returns to 0. Thus
\[
  \mathbb E_0[C]=\frac1a+\frac1b,
  \qquad m(0)=\frac1a,\quad m(1)=\frac1b.
\]
Normalizing gives
\[
  \pi(0)=\frac{b}{a+b},\qquad
  \pi(1)=\frac{a}{a+b},
\]
the same stationary distribution obtained by solving detailed balance. The cycle argument recovers it from time spent in each state rather than from edge flows.

The occupation rates have a direct interpretation. If departure from 0 is slow, each cycle spends a long time at 0; if return from 1 is slow, it spends a long time at 1. Stationary mass is proportional to expected time per cycle, not to the number of jumps or visits.

## 5. Worked example: a directed three-cycle

Consider (0\to1\to2\to0) with rates a,b,c, respectively. Regeneration at 0 produces a deterministic sequence of states between holding times. One cycle contains an exponential wait of mean 1/a at state 0, then 1/b at state 1, and 1/c at state 2. Its expected length is
\[
  \mathbb E_0[C]=\frac1a+\frac1b+\frac1c.
\]
The cycle occupation probabilities are therefore proportional to (1/a,1/b,1/c), or equivalently to (bc,ca,ab). This matches the directed tree weights from Chapter 68.

The agreement is instructive. The tree theorem counts weighted ways of flowing into each state, while regeneration measures expected time spent there during a typical cycle. Both produce the stationary law, but their proof obligations differ: trees are finite combinatorics and determinants; cycles use strong Markov restart and integrability.

### Worked example: branching excursions from a hub

Let state 0 jump to 1 at rate a or to 2 at rate b. From 1 return to 0 at rate c, and from 2 return to 0 at rate d, with all four rates positive. A cycle at 0 first waits an exponential time of mean (1/(a+b)). It then chooses branch 1 with probability (a/(a+b)) or branch 2 with probability (b/(a+b)). The expected cycle occupations are
\[
  m(0)=\frac1{a+b},\qquad
  m(1)=\frac{a}{(a+b)c},\qquad
  m(2)=\frac{b}{(a+b)d}.
\]
After normalization, the stationary masses are proportional to (cd,ad,bc). The branching probabilities at the hub and the mean excursion durations combine multiplicatively. This example is a concrete instance of the killed Green formula: departure chooses an initial point, then the Green kernel measures the expected excursion occupation before return.

## 6. Excursion occupation from a killed Green kernel

The cycle formula can be computed from the process killed on returning to a. Let (S_a=S\setminus\{a\}), and let K be the subgenerator on S_a, with transitions back to a counted as killing. The initial holding at a contributes expected time (1/q_a) to m(a). At departure, the first state j has probability
\[
  p(a,j)=\frac{q(a,j)}{q_a}.
\]
For i∈S_a, the expected excursion time in i starting from j is the zero-discount Green entry (G_0(j,i)=(-K)^{-1}(j,i)). Hence
\[
  m(a)=\frac1{q_a},\qquad
  m(i)=\sum_{j\in S_a}p(a,j)G_0(j,i)\quad(i\ne a).
\]
The expected cycle length is ∑_i m(i). This gives a direct computational method for stationary probabilities using one killed linear system.

The formula also explains how the reference state affects the representation but not the result. Choosing a different regeneration state changes the excursion Green matrix and the cycle length, while the normalized occupation vector remains the unique stationary distribution. In a formal development, prove the formula for arbitrary a and only then select a convenient state for a particular model.

## 7. The renewal-reward theorem

Let (R_f^{(n)}) and (C_n) be the reward and duration of cycle n. The pairs are i.i.d., with finite first moments. At the end of n cycles,
\[
  \frac{\sum_{k=1}^nR_f^{(k)}}{\sum_{k=1}^nC_k}
       \longrightarrow\frac{\mathbb E[R_f]}{\mathbb E[C]}
\quad\text{almost surely},
\]
by the strong law of large numbers. The incomplete final cycle contributes a negligible fraction of elapsed time under the finite-mean renewal-reward theorem. Therefore
\[
  \frac1T\int_0^T f(X_t)\,dt\longrightarrow\pi(f)
\quad\text{almost surely}.
\]
This derives the ergodic average from independent cycles. It complements Birkhoff’s theorem: the regenerative proof uses the chain’s return structure, while the ergodic theorem uses stationarity and measure-preserving shift dynamics.

For bounded f on a finite chain, the cycle reward is bounded in absolute value by \(\lVert f\rVert_\infty C\), so its expectation is finite. The strong law applies to both rewards and lengths. To control the terminal partial cycle, use a standard renewal-reward theorem or prove that the length of the cycle containing T divided by T tends to zero almost surely. The latter follows from finite cycle moments; it should not be replaced by the unsupported assertion that the unfinished cycle is bounded.

## 8. Regenerative central limit theorem

The cycle decomposition also gives a central limit theorem. Let μ=π(f) and define the centered reward of cycle n by
\[
  Y_n=R_f^{(n)}-\mu C_n.
\]
Then \(\mathbb E[Y_n]=0\). If the cycle reward and length have finite second moments, the i.i.d. central limit theorem applied to \(\sum_{k=1}^nY_k\), together with the renewal estimate \(N(T)/T\to1/\mathbb E[C]\), yields
\[
  \sqrt T\left(\frac1T\int_0^T f(X_t)\,dt-\mu\right)
    \Rightarrow\mathcal N\left(0,
       \frac{\operatorname{Var}(Y_1)}{\mathbb E[C]}\right).
\]
For finite irreducible chains, cycle lengths have geometric tails at a fixed time scale, so bounded f gives the required moments. The terminal incomplete cycle must still be shown negligible at the √T scale; finite second moments provide the standard estimate.

This formula gives an interpretable asymptotic variance: each cycle contributes a centered reward, and cycles arrive at asymptotic rate (1/\mathbb E[C]). It is often easier to estimate from simulated regeneration cycles than to solve a Poisson equation, especially when the regeneration point is observable. Conversely, the Poisson equation can compute the same asymptotic variance through spectral methods. Showing these formulas agree is a useful advanced exercise.

The regenerative CLT is more delicate than the law of large numbers. The latter needs only first moments; the normal limit uses second moments and a negligible-remainder theorem. A Lean library should expose those moment assumptions explicitly rather than proving a stronger theorem under hidden finite-state shorthand.

### Two-state check of the asymptotic variance

Return to the chain \(0\to1\) at rate a and \(1\to0\) at rate b, and take \(f=\mathbf1_{\{1\}}\). A cycle contains independent holding times \(H_0\sim\mathrm{Exp}(a)\) and \(H_1\sim\mathrm{Exp}(b)\). Its length is \(C=H_0+H_1\), its reward is \(R_f=H_1\), and its mean reward rate is \(\mu=a/(a+b)\). The centered cycle reward is
\[
  Y=R_f-\mu C=\frac{b}{a+b}H_1-\frac{a}{a+b}H_0.
\]
Independence and the exponential variances give \(\operatorname{Var}(Y)=2/(a+b)^2\), while \(\mathbb E[C]=(a+b)/(ab)\). The asymptotic variance of the time average is therefore \(2ab/(a+b)^3\). Directly, the stationary variance of f is \(ab/(a+b)^2\), and its covariance decays at rate a+b, giving the same integrated covariance \(2ab/(a+b)^3\). This is a useful cross-check between regenerative and semigroup derivations.

More explicitly, the stationary covariance at lag t is \(\operatorname{Cov}_\pi(f(X_0),f(X_t))=ab(a+b)^{-2}e^{-(a+b)t}\). The asymptotic variance convention used here is twice the integral of this covariance over nonnegative lags. A common source of factor-of-two errors is to report the one-sided integral as the variance. Keeping the convention in the theorem statement makes comparisons with spectral formulas and simulation output unambiguous.

## 9. Formalizing return cycles

The process-level definitions should distinguish the first departure from the first return. For a chain started at a, define D as the first exit from a and C as the first hit of a at or after D. If the state type is finite and the chain has positive exit rate from a, then D is positive almost surely. For a one-state chain, no such departure exists; handle it as a separate trivial case or require at least two states and irreducibility.

Keep the probabilistic data explicit in the Lean interface. A cycle record can contain its duration, a measurable path segment, and proofs that the path starts and ends at a and does not visit a in between. A reward function then maps that segment to an integral, while integrability is stated separately for duration and reward. This lets the stationary-law theorem depend only on expected occupation and the stopped-generator identity; the strong law and central limit theorem can be developed later without changing the cycle representation. For computational examples, the finite-state Green formula can calculate the occupation vector independently of path-space construction.

The proof architecture is:

```text
finite irreducible chain ──> finite-mean return cycle ──> cycle occupation m
             │                         │                       │
             v                         v                       v
     strong Markov restart       Dynkin at C             m Q = 0
                                                             │
                                                             v
                                                normalized stationary law
                                                             │
                                                             v
                                                 renewal-reward averages
```

To avoid importing a full strong-law theorem into the stationary-law proof, first prove πQ=0 from stopped Dynkin’s formula. The renewal-reward limit is a separate theorem that consumes the i.i.d. cycles. Similarly, the Green-kernel formula for m is a finite matrix calculation and can be completed before constructing sample paths.

## 10. Common failure modes

### Return time is defined as zero at the starting state

In continuous time, starting at a makes τₐ=0 if the hitting set includes time zero. Define departure first, then the next return.

### Cycle rewards are confused with jump counts

Stationary mass is expected time occupation divided by cycle length. Visit counts need holding-time weights.

### Dynkin’s formula is stopped at an unbounded time without limits

Use C∧T and justify convergence using bounded f, bounded Qf, and finite expected C.

### The reference state is assumed to affect stationarity

Cycle descriptions depend on the chosen regeneration state; their normalized occupation vectors agree by uniqueness.

### A finite expected cycle length is assumed without irreducibility

Transient or closed classes can make return probability zero or return time infinite. State the finite irreducible hypotheses.

## 11. Exercises

1. Define a return cycle using departure and return times and prove C>0 almost surely.
2. Prove finite expected return time for a finite irreducible chain using a uniform hitting probability.
3. Derive mQ=0 by applying Dynkin’s formula at C∧T and passing to the limit.
4. Recover the two-state stationary law from expected cycle occupation.
5. Compute cycle occupation for the directed three-cycle and compare with its tree weights.
6. Derive the excursion Green formula for m(i) away from the regeneration state.
7. Prove the renewal-reward limit for bounded f using i.i.d. cycle rewards.
8. Explain why expected visit counts alone do not determine continuous-time stationary mass.
9. Identify the separate one-state case when the reference state has zero exit rate.
10. Design a Lean structure containing a cycle length, cycle reward, and integrability proofs.

## Summary

A finite irreducible chain regenerates whenever it returns to a reference state after departing. Successive cycles are i.i.d.; expected occupation in one cycle, normalized by expected cycle length, is stationary. Stopped Dynkin’s formula proves the occupation vector lies in the left kernel of the generator, and the strong law yields time-average convergence. Excursion occupation can also be computed using the killed Green kernel from Chapter 72. The central formalization tasks are precise return-time definitions, finite-mean estimates, and a justified optional-sampling limit.

## Further reading

- Chapters 37, 58, and 72 for stopping times, generator martingales, and Green kernels.
- Chapters 47 and 46 for ergodic averages and measure-preserving dynamics.
