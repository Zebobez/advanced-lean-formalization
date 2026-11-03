# Chapter 85 — Performance Measures from Matrix-Geometric Tails

> **Audience.** This chapter assumes familiarity with stationary level vectors, matrix-geometric solutions, and basic queueing performance measures. It starts from a stationary law of the form \(\pi_n=\pi_0R^n\) and derives tail probabilities, phase marginals, generating functions, and moments.

A rate matrix is useful because it compresses an infinite stationary distribution into a finite matrix and a boundary vector. That compression becomes practical when we extract quantities such as the probability that a queue exceeds a threshold, the mean level, or a phase-specific cost. These are not new queueing models: they are reusable calculations applied to the stationary representation developed in Chapters 79 and 84.

The central discipline is to keep four objects distinct: the rate matrix \(R\), the boundary row vector \(\pi_0\), the full phase-marginal vector, and the scalar probability of a level event. Matrix order matters in the first three; summing over phases produces the fourth.

## Learning objectives

After this chapter, you should be able to:

- derive exact tail vectors from a matrix-geometric stationary law;
- compute a level probability generating function and its first two moments;
- evaluate phase-specific and level-weighted performance measures;
- distinguish stationary level distributions from arrival-epoch observations;
- organize infinite-series arguments separately from finite matrix identities in Lean.

## 1. From a rate matrix to a stationary law

Let the phase set be finite with \(m\) elements. Suppose a stationary distribution is given by row vectors

\[
\pi_n=\pi_0R^n,\qquad n\geq0,
\tag{85.1}
\]

where \(\pi_0\) is a nonnegative row vector and \(R\) is a nonnegative \(m\times m\) matrix with spectral radius \(\rho(R)<1\). Write \(\mathbf1\) for the all-ones column vector. The total mass is

\[
\sum_{n=0}^{\infty}\pi_n\mathbf1
=\pi_0\left(\sum_{n=0}^{\infty}R^n\right)\mathbf1
=\pi_0(I-R)^{-1}\mathbf1.
\tag{85.2}
\]

For (85.1) to be a probability law, the last quantity must equal one. This is the normalization condition. In a queueing model, \(\pi_0\) is generally found from a boundary equation and then normalized; it should not be inferred from \(R\) alone.

The full phase-marginal row vector is

\[
q=\sum_{n=0}^{\infty}\pi_n
=\pi_0(I-R)^{-1}.
\tag{85.3}
\]

Its entries are the probabilities of the individual phases after summing over all levels, and \(q\mathbf1=1\). The matrix \(R\) is not itself generally a stochastic phase transition matrix. It propagates stationary mass between adjacent levels, and its row sums need not equal one.

The calculation path is:

~~~text
boundary vector and rate matrix
             |
             v
       level mass pi_n
        /           \
       v             v
 tail vectors      generating function
       |             |
       +-------> moments and costs
~~~

Each arrow uses a convergence fact as well as a finite matrix identity. We will make those parts explicit.

## 2. Tail probabilities and threshold events

For \(K\geq0\), define the phase-resolved tail row vector

\[
\tau_K=\sum_{n=K}^{\infty}\pi_n.
\tag{85.4}
\]

Substitute (85.1), write \(n=K+j\), and factor the matrix powers:

\[
\tau_K
=\pi_0\sum_{j=0}^{\infty}R^{K+j}
=\pi_0R^K\sum_{j=0}^{\infty}R^j
=\pi_0R^K(I-R)^{-1}.
\tag{85.5}
\]

The probability that the level is at least \(K\) is therefore

\[
\mathbb P(L\geq K)=\tau_K\mathbf1
=\pi_0R^K(I-R)^{-1}\mathbf1.
\tag{85.6}
\]

If the service requirement is “fewer than \(K\) customers,” the failure event is \(L\geq K\), not \(L>K\). The latter is the tail at \(K+1\). Keeping this off-by-one distinction visible is useful when translating a service-level requirement into a theorem.

The vector in (85.5) gives more detail than the scalar in (85.6). If \(c\) is a column vector whose entries mark a set of phases, then

\[
\mathbb P(L\geq K,\ J\in C)=\tau_Kc.
\tag{85.7}
\]

Here \(c_j=1\) for a phase in \(C\) and \(c_j=0\) otherwise. If \(q_j>0\), the conditional exceedance probability in phase \(j\) is \((\tau_K)_j/q_j\). This supports questions such as “how often does the system exceed the capacity threshold while the environment is in its slow-service phase?”

An immediate recurrence follows from (85.5):

\[
\tau_{K+1}=\tau_KR.
\tag{85.8}
\]

This is a phase-vector recurrence, not generally a scalar geometric recurrence. The scalar tails need not have a constant ratio from one threshold to the next.

### Truncating a computation at a maximum level

Suppose a numerical calculation retains only levels \(0,\ldots,N\). Its omitted probability mass is not an unknown residual: it is exactly \(\tau_{N+1}\mathbf1\). For a bounded reward \(f\) with \(|f|\leq M\), omitting the tail changes the unnormalized expectation by at most \(M\,\tau_{N+1}\mathbf1\). If the retained probabilities are renormalized to sum to one, the difference from the full expectation is at most \(2M\,\tau_{N+1}\mathbf1\), provided the retained mass is positive. The factor two accounts for changing both the retained and omitted conditional averages.

This estimate is appropriate for bounded costs such as a phase indicator or a capped penalty. Queue length itself is unbounded, so its truncation error should be bounded with a weighted tail or moment estimate rather than the bounded-reward inequality.

### Exact tails and certified bounds

If \(\pi_0\) and \(R\) are exact, (85.6) is an exact tail formula. If they are computed with error bounds, a rigorous enclosure requires propagating those errors through \(R^K\) and \((I-R)^{-1}\). Chapter 80 develops certified matrix computation and tail bounds for QBDs; the same separation is useful here: first prove the identity, then bound the numerical error in each matrix operation.

For compatible row, matrix, and column norms, one crude bound is:

\[
\mathbb P(L\geq K)
\leq \|\pi_0\|\,\|R^K\|\,\|(I-R)^{-1}\|\,\|\mathbf1\|.
\tag{85.9}
\]

The inequality is useful only when the chosen norm controls the powers well. It is possible that \(\rho(R)<1\) while a familiar matrix norm has \(\|R\|\geq1\). A certified proof should use an appropriate norm, a power bound, or a direct interval enclosure rather than assuming one-step contraction.

## 3. Probability generating functions

The phase-vector probability generating function is

\[
\Pi(z)=\sum_{n=0}^{\infty}z^n\pi_n
=\pi_0\sum_{n=0}^{\infty}(zR)^n
=\pi_0(I-zR)^{-1},
\tag{85.10}
\]

whenever the matrix series converges; in finite dimension it converges for \(|z|\rho(R)<1\). Multiplying by \(\mathbf1\) gives the scalar generating function of the level:

\[
G(z)=\mathbb E[z^L]
=\pi_0(I-zR)^{-1}\mathbf1.
\tag{85.11}
\]

Because \(\rho(R)<1\), the convergence region includes an open neighborhood of \(z=1\). Differentiating there yields the first moment:

\[
\mathbb E[L]
=G'(1)
=\pi_0R(I-R)^{-2}\mathbf1.
\tag{85.12}
\]

The second derivative gives the second factorial moment:

\[
\mathbb E[L(L-1)]
=G''(1)
=2\pi_0R^2(I-R)^{-3}\mathbf1.
\tag{85.13}
\]

Since \(L^2=L(L-1)+L\), the second raw moment and variance are

\[
\mathbb E[L^2]
=\pi_0R(I+R)(I-R)^{-3}\mathbf1,
\tag{85.14}
\]

\[
\operatorname{Var}(L)=\mathbb E[L^2]-(\mathbb E[L])^2.
\tag{85.15}
\]

The powers of \(I-R\) are resolvents, not entrywise reciprocals. Since \(R\) commutes with \(I-R\) and its inverse, expressions such as \(R(I-R)^{-2}\) are unambiguous as matrix products. The factor order should still be preserved in a formal proof, where matrices are not commutative in general.

The same method gives all polynomial moments. For example, a third derivative gives \(\mathbb E[L(L-1)(L-2)]\). As \(\rho(R)<1\), every polynomially weighted series \(\sum_n n^p\pi_0R^n\) converges for a nonnegative integer \(p\). The exact expression can be obtained from higher derivatives or from repeated Cauchy products.

There is also a tail-sum check on the mean. For a nonnegative integer-valued level,

\[
\mathbb E[L]=\sum_{K=1}^{\infty}\mathbb P(L\geq K).
\tag{85.16a}
\]

Substituting (85.6) and summing the matrix powers gives

\[
\sum_{K=1}^{\infty}\pi_0R^K(I-R)^{-1}\mathbf1
=\pi_0R(I-R)^{-2}\mathbf1,
\]

which agrees with (85.12). This derivation offers an independent proof path: a Lean development can first formalize the tail-sum identity for natural-valued random variables, then use the geometric tail formula. Agreement between the tail and generating-function derivations is a useful check on index conventions.

## 4. Phase-specific costs and level-weighted rewards

Let \(c\) be a column vector assigning a cost to each phase. If the cost depends only on the phase, the stationary expected cost is

\[
\mathbb E[c_J]
=\sum_{n=0}^{\infty}\pi_nc
=\pi_0(I-R)^{-1}c.
\tag{85.16}
\]

If the phase cost is incurred once per customer or once per unit of level, the expected level-weighted cost is

\[
\mathbb E[Lc_J]
=\sum_{n=0}^{\infty}n\pi_nc
=\pi_0R(I-R)^{-2}c.
\tag{85.17}
\]

These formulas let the modeler distinguish a high queue level in a fast environment from the same level in a costly or slow environment. For example, \(c_j\) could record energy use per occupied server, a penalty for a congestion phase, or an indicator that a service resource is unavailable.

For a threshold penalty that charges \(c_J\) only when \(L\geq K\), use

\[
\mathbb E[\mathbf1_{\{L\geq K\}}c_J]
=\tau_Kc
=\pi_0R^K(I-R)^{-1}c.
\tag{85.18}
\]

This is often simpler than summing the level probabilities one by one. It also makes the state-dependent objective explicit as a column vector, which is a natural interface for theorem statements in Lean.

## 5. Worked example: the M/M/1 stationary tail

Let arrivals be Poisson with rate \(\lambda\), service be exponential with rate \(\mu\), and assume \(\lambda<\mu\). The stationary number of customers in the system has a one-phase matrix-geometric representation with scalar rate \(r=\rho=\lambda/\mu\) and boundary mass \(1-\rho\):

\[
\pi_n=(1-\rho)\rho^n.
\tag{85.19}
\]

Substituting into (85.6) gives, for every \(K\geq0\),

\[
\mathbb P(L\geq K)
=(1-\rho)\sum_{n=K}^{\infty}\rho^n
=\rho^K.
\tag{85.20}
\]

The expected level is

\[
\mathbb E[L]
=(1-\rho)\sum_{n=0}^{\infty}n\rho^n
=\frac{\rho}{1-\rho},
\tag{85.21}
\]

and the variance is

\[
\operatorname{Var}(L)=\frac{\rho}{(1-\rho)^2}.
\tag{85.22}
\]

For instance, a threshold target \(\mathbb P(L\geq K)\leq\varepsilon\) becomes \(\rho^K\leq\varepsilon\). The least integer \(K\) satisfying it is found by a logarithm and a ceiling, with care around equality and floating-point rounding in a certified implementation.

The matrix formula generalizes this scalar calculation. In multiple phases, the tail is usually a sum of interacting phase contributions; a single scalar \(\rho\) no longer captures every finite-threshold probability.

### Sampling epoch matters

For the M/M/1 model, Poisson arrivals see time averages, so the arrival-epoch queue distribution agrees with the stationary time distribution under the standard assumptions. For general renewal arrivals, this agreement need not hold. If \(R\) came from a prearrival embedded chain, then (85.6) is a prearrival tail. Converting it into an arbitrary-time tail may require a renewal-reward or supplementary-variable argument. The rate matrix does not erase the sampling-epoch distinction discussed in Chapter 81.

## 6. Worked example: two phases with different decay rates

Consider a normalized matrix-geometric probability law with

\[
R=\begin{pmatrix}1/4&0\\0&1/2\end{pmatrix},
\qquad
\pi_0=\begin{pmatrix}3/8&1/4\end{pmatrix}.
\tag{85.23}
\]

The two phase contributions have total masses

\[
\frac{3/8}{1-1/4}=\frac12,
\qquad
\frac{1/4}{1-1/2}=\frac12,
\]

so (85.2) gives total mass one. This example isolates the performance calculations; it is not intended as a specification of a particular queue transition boundary.

The probability generating function is

\[
G(z)=\frac{3/8}{1-z/4}+\frac{1/4}{1-z/2}.
\tag{85.24}
\]

At threshold \(K\), the tail is

\[
\mathbb P(L\geq K)
=\frac12\left(\frac14\right)^K
+\frac12\left(\frac12\right)^K.
\tag{85.25}
\]

The two phases each have stationary mass \(1/2\), but their conditional level distributions decay at different rates. The mean is

\[
\mathbb E[L]
=\frac12\frac{1/4}{1-1/4}
+\frac12\frac{1/2}{1-1/2}
=\frac16+\frac12
=\frac23.
\tag{85.26}
\]

The second moment is

\[
\mathbb E[L^2]
=\frac12\frac{(1/4)(1+1/4)}{(1-1/4)^2}
+\frac12\frac{(1/2)(1+1/2)}{(1-1/2)^2}
=\frac{16}{9},
\]

and \(\operatorname{Var}(L)=16/9-(2/3)^2=4/3\). At a high threshold, the second phase dominates the tail because its decay factor \(1/2\) is larger than \(1/4\). The phase mixture is invisible if one retains only the average level.

### 6.1 An executable two-phase performance certificate

For the example above, R is diagonal with decay factors 1/4 and 1/2, and the boundary vector has entries 3/8 and 1/4. Each phase contributes total mass 1/2. The code checks the resulting tail at level three, shows that successive scalar tail ratios differ, and verifies the probability generating function and the first two moments as exact rational expressions. The closed forms use the scalar geometric-series and moment identities from Sections 2–3; this certificate checks their arithmetic, not the analytic convergence argument.

```lean
def phaseAInitialMass : ℚ := 3 / 8
def phaseBInitialMass : ℚ := 1 / 4
def phaseADecay : ℚ := 1 / 4
def phaseBDecay : ℚ := 1 / 2

def phaseATail (k : Nat) : ℚ := (1 / 2) * phaseADecay ^ k
def phaseBTail (k : Nat) : ℚ := (1 / 2) * phaseBDecay ^ k
def twoPhaseTail (k : Nat) : ℚ := phaseATail k + phaseBTail k

def phaseAMeanContribution : ℚ :=
  (1 / 2) * phaseADecay / (1 - phaseADecay)
def phaseBMeanContribution : ℚ :=
  (1 / 2) * phaseBDecay / (1 - phaseBDecay)
def twoPhaseMean : ℚ := phaseAMeanContribution + phaseBMeanContribution

def phaseASecondContribution : ℚ :=
  (1 / 2) * phaseADecay * (1 + phaseADecay) / (1 - phaseADecay) ^ 2
def phaseBSecondContribution : ℚ :=
  (1 / 2) * phaseBDecay * (1 + phaseBDecay) / (1 - phaseBDecay) ^ 2
def twoPhaseSecondMoment : ℚ := phaseASecondContribution + phaseBSecondContribution
def twoPhaseVariance : ℚ := twoPhaseSecondMoment - twoPhaseMean ^ 2

def twoPhasePGF (z : ℚ) : ℚ :=
  (3 / 8) / (1 - z / 4) + (1 / 4) / (1 - z / 2)

theorem phaseA_stationary_mass : phaseAInitialMass / (1 - phaseADecay) = 1 / 2 := by
  norm_num [phaseAInitialMass, phaseADecay]

theorem phaseB_stationary_mass : phaseBInitialMass / (1 - phaseBDecay) = 1 / 2 := by
  norm_num [phaseBInitialMass, phaseBDecay]

theorem twoPhase_total_mass :
    phaseAInitialMass / (1 - phaseADecay) +
      phaseBInitialMass / (1 - phaseBDecay) = 1 := by
  rw [phaseA_stationary_mass, phaseB_stationary_mass]
  norm_num

theorem phaseATail_succ (k : Nat) : phaseATail (k + 1) = phaseATail k / 4 := by
  unfold phaseATail phaseADecay
  rw [pow_succ]
  ring

theorem phaseBTail_succ (k : Nat) : phaseBTail (k + 1) = phaseBTail k / 2 := by
  unfold phaseBTail phaseBDecay
  rw [pow_succ]
  ring

theorem twoPhase_tail_at_three : twoPhaseTail 3 = 9 / 128 := by
  norm_num [twoPhaseTail, phaseATail, phaseBTail, phaseADecay, phaseBDecay]

theorem twoPhase_tail_ratios_differ :
    twoPhaseTail 1 / twoPhaseTail 0 ≠ twoPhaseTail 2 / twoPhaseTail 1 := by
  norm_num [twoPhaseTail, phaseATail, phaseBTail, phaseADecay, phaseBDecay]

theorem twoPhase_pgf_at_one : twoPhasePGF 1 = 1 := by
  norm_num [twoPhasePGF]

theorem phaseA_mean_is_one_sixth : phaseAMeanContribution = 1 / 6 := by
  norm_num [phaseAMeanContribution, phaseADecay]

theorem phaseB_mean_is_one_half : phaseBMeanContribution = 1 / 2 := by
  norm_num [phaseBMeanContribution, phaseBDecay]

theorem twoPhase_mean_is_two_thirds : twoPhaseMean = 2 / 3 := by
  rw [twoPhaseMean, phaseA_mean_is_one_sixth, phaseB_mean_is_one_half]
  norm_num

theorem phaseA_second_moment_is_five_eighteenths :
    phaseASecondContribution = 5 / 18 := by
  norm_num [phaseASecondContribution, phaseADecay]

theorem phaseB_second_moment_is_three_halves :
    phaseBSecondContribution = 3 / 2 := by
  norm_num [phaseBSecondContribution, phaseBDecay]

theorem twoPhase_second_moment_is_sixteen_ninths : twoPhaseSecondMoment = 16 / 9 := by
  rw [twoPhaseSecondMoment, phaseA_second_moment_is_five_eighteenths,
    phaseB_second_moment_is_three_halves]
  norm_num

theorem twoPhase_variance_is_four_thirds : twoPhaseVariance = 4 / 3 := by
  rw [twoPhaseVariance, twoPhase_second_moment_is_sixteen_ninths,
    twoPhase_mean_is_two_thirds]
  norm_num
```

The differing ratios are a concrete check that a phase mixture can have a tail that is not scalar-geometric even though each conditional phase tail is geometric. The moment calculation also preserves the distinction between the second moment (16/9) and the variance (4/3).

## 7. Lean proof architecture

### 7.1 Separate representation from normalization

Represent the level mass by a function \(n\mapsto \pi_0R^n\). Keep the matrix type, row-vector type, and all-ones column explicit. A representation theorem should assume:

- finite phase type;
- nonnegativity of \(\pi_0\) and \(R\);
- convergence of the matrix power series;
- the normalization equation \(\pi_0(I-R)^{-1}\mathbf1=1\).

Do not package a rate equation and a stationary distribution into one opaque definition. A rate equation derives the interior balance; boundary balance establishes compatibility at low levels; normalization makes the total mass a probability. The distinction is useful for both reuse and error diagnosis.

### 7.2 Prove tails by shifting a convergent series

For each fixed \(K\), first prove a finite partial-sum identity:

\[
\sum_{n=K}^{N}R^n=R^K\sum_{j=0}^{N-K}R^j.
\]

Then pass to the limit using convergence of \(\sum_n R^n\). This keeps the index reorganization finite and elementary. In a Lean proof, identify the exact sequence being summed and provide a theorem that its partial sums converge to the matrix inverse. A library theorem about the Neumann series may discharge the final step once the norm or spectral-radius hypothesis is in the required form.

The scalar tail theorem follows by multiplying the row-vector identity by \(\pi_0\) on the left and \(\mathbf1\) on the right. Prove the phase-resolved equation first; obtain scalar event probabilities by a final dot product. This produces a more reusable result than a theorem that proves only one scalar formula.

### 7.3 Derive moments without entrywise matrix calculus

There are two clean proof routes for (85.12)–(85.14):

1. differentiate the matrix-valued generating series inside its convergence region, then evaluate at one;
2. use absolutely convergent Cauchy products and count how many tuples of indices contribute to each matrix power.

The second route exposes the combinatorics. If \(S=\sum_{n\geq0}R^n=(I-R)^{-1}\), then

\[
SRS=\sum_{n\geq1}nR^n,
\qquad
2R^2S^3=\sum_{n\geq2}n(n-1)R^n.
\tag{85.27}
\]

For the first identity, the coefficient \(R^n\) appears once for each pair of nonnegative integers \(a,b\) with \(a+b=n-1\), giving \(n\) occurrences. For the second, it appears for each triple whose sum is \(n-2\), giving \(\binom n2\) occurrences before multiplication by two.

Formalizing these identities requires absolute convergence to rearrange infinite matrix sums. For a finite truncation, use finite sums and exact coefficient counts. Then prove a convergence bound for the tails, or use a theorem on products of absolutely summable series. Avoid rewriting a countable sum as a Cauchy product without recording the summability condition.

### 7.4 Make the output a performance API

A useful library interface exposes separate operations for:

- level mass at \(n\);
- phase-resolved tail at threshold \(K\);
- scalar threshold probability;
- phase marginal;
- level mean and second factorial moment;
- expected phase cost and level-weighted phase cost.

Each operation should come with its assumptions. For example, a bounded phase cost only needs the normalized stationary law, while the unbounded cost \(L\) needs the first weighted series to converge. In this finite-dimensional geometric setting \(\rho(R)<1\) supplies all polynomial moments, but the theorem should still name the convergence result it uses.

## 8. Common failure modes

1. **Calling \(R\) a stochastic phase matrix.** It usually is not; it is a level-to-level rate matrix.
2. **Dropping the boundary vector.** The tail and moment formulas depend on \(\pi_0\), not just on \(R\).
3. **Summing the wrong event.** \(L\geq K\) starts its series at \(K\); \(L>K\) starts at \(K+1\).
4. **Multiplying in a convenient but invalid order.** Matrix factors cannot be rearranged as scalars can.
5. **Using \((I-R)^{-1}\) without convergence.** The spectral-radius or Neumann-series hypothesis is essential.
6. **Taking derivatives at a boundary point without a neighborhood.** Here \(\rho(R)<1\) ensures the generating series converges around \(z=1\); a weaker domain may not.
7. **Confusing level mass with phase probability.** Sum over levels for the phase marginal; sum over phases for the level marginal.
8. **Inferring arbitrary-time performance from an embedded chain.** The observation epoch must match the quantity being reported.
9. **Applying a norm bound blindly.** \(\rho(R)<1\) does not imply \(\|R\|<1\) for every selected norm.
10. **Rearranging a conditionally convergent matrix series.** The Cauchy-product proof needs absolute convergence.

## 9. Exercises

1. Prove the tail-vector formula (85.5) using finite partial sums and a limit.
2. For a phase cost vector \(c\), derive (85.16) and (85.18).
3. Starting from \(G(z)\), derive the first and second factorial moment formulas.
4. Verify the M/M/1 tail and variance in (85.20)–(85.22) directly from the scalar geometric series.
5. For the two-phase law (85.23), compute the phase-specific exceedance probabilities and their conditional versions.
6. Show that \(\tau_{K+1}=\tau_KR\). Give an example where the scalar ratio \(\mathbb P(L\geq K+1)/\mathbb P(L\geq K)\) is not constant.
7. Prove the first Cauchy-product identity in (85.27) for finite partial sums and identify the convergence lemma needed for the infinite limit.
8. Formalize the distinction between \(\mathbb P(L\geq K)\) and \(\mathbb P(L>K)\) for natural-number levels.
9. Suppose \(c\) is a nonnegative phase-cost vector. Interpret \(\pi_0R(I-R)^{-2}c\) and state when it is finite.
10. Explain what extra sampling or renewal argument is required to turn a prearrival tail into an arbitrary-time tail in a GI/M/1 queue.

## 10. Summary

Once a stationary law has the matrix-geometric form \(\pi_n=\pi_0R^n\) with \(\rho(R)<1\), its performance measures reduce to resolvents and their powers. The phase-resolved tail is \(\pi_0R^K(I-R)^{-1}\); the scalar tail follows by multiplying by \(\mathbf1\). The generating function gives the mean, factorial moments, and variance, while phase-cost vectors express additional objectives.

In Lean, prove the matrix-series convergence and index shifts explicitly, then reuse the resulting resolvent identities for tails, moments, and costs. The formulas are compact, but their reusable proof depends on preserving matrix order and stating the correct convergence and observation-epoch assumptions.

### Further reading

- M. F. Neuts, [“Markov chains with applications in queueing theory, which have a matrix-geometric invariant probability vector”](https://doi.org/10.2307/1426725), *Advances in Applied Probability* 10 (1978), 185–212. This paper establishes the matrix-geometric invariant-vector framework used for the stationary representation.
- M. F. Neuts, [“The probabilistic significance of the rate matrix in matrix-geometric invariant vectors”](https://doi.org/10.2307/3212949), *Journal of Applied Probability* 17 (1980), 291–296. This note gives a probabilistic interpretation of the rate matrix in terms of level-crossing visits.
- M. F. Neuts, [“Stationary waiting-time distributions in the GI/PH/1 queue”](https://doi.org/10.2307/3213064), *Journal of Applied Probability* 18 (1981), 901–912. This paper connects matrix-geometric embedded-chain solutions to queueing waiting-time quantities.
