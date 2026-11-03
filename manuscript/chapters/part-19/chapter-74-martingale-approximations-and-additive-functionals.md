# Chapter 74 — Martingale Approximations for Additive Functionals

> **Audience.** This chapter assumes finite-state continuous-time Markov chains, generator martingales, invariant distributions, and the Poisson equation. It connects long-time fluctuations of path integrals to martingale limit theorems.

For a chain \((X_t)\) and an observable \(f\), the time average \(T^{-1}\int_0^T f(X_t)\,dt\) converges to its stationary mean under standard irreducibility assumptions. The next question is how its error scales. In a finite irreducible chain, the centered additive functional can be written as a martingale plus a bounded endpoint correction. The martingale has an explicit quadratic variation, which identifies the asymptotic variance and leads to a central limit theorem.

This is a complementary route to Chapter 73’s regenerative central limit theorem. Regeneration groups a trajectory into independent cycles; the martingale method spreads the contribution across time and uses the generator. It is often easier to generalize to several observables and gives formulas suited to spectral and variance analysis.

## Learning objectives

By the end of the chapter, you should be able to:

- solve the centered Poisson equation for a finite irreducible generator;
- decompose an additive functional into a martingale and a boundary term;
- compute the asymptotic variance from the carré du champ;
- verify the formula in reversible and non-reversible examples;
- formulate a vector-valued central limit theorem;
- separate the algebraic, martingale, and ergodic interfaces in Lean.

## 1. Additive functionals and fluctuation scale

Let Q be the generator of a finite irreducible continuous-time chain, with semigroup \(P_t=e^{tQ}\) and stationary distribution \(\pi\). For a function \(f:S\to\mathbb R\), write \(\mu=\pi(f)\) and \(g=f-\mu\mathbf1\). The centered time integral is
\[
  A_T=\int_0^T g(X_t)\,dt.
\]
The law of large numbers says \(A_T/T\to0\). Under mixing, fluctuations are typically of order \(\sqrt T\), so one seeks a limit for \(A_T/\sqrt T\).

The finite-state setting removes several analytic obstacles. Every function is bounded, jump rates have a finite maximum, and irreducibility gives exponential convergence of the semigroup to equilibrium. Yet an effective proof still has three distinct parts: an algebraic solution of a Poisson equation, a pathwise martingale identity, and a martingale central limit theorem. Combining them too early makes hypotheses and sign conventions difficult to track.

For the central limit theorem, the chain may start from any fixed state. The transient initial segment contributes a bounded-scale correction after the Poisson decomposition. Starting in stationarity simplifies covariance calculations but is not required for the martingale limit.

## 2. The centered Poisson equation

Since \(\pi(g)=0\), solve
\[
  -Qh=g,\qquad \pi(h)=0.
\]
The first equation determines h only up to an additive constant because \(Q\mathbf1=0\); the second selects a unique centered solution. On a finite irreducible chain, the kernel of Q consists exactly of constants, and its range is the subspace of π-centered functions. Thus the restricted map \(-Q\) is invertible on that subspace.

One construction is the convergent integral
\[
  h=\int_0^\infty P_tg\,dt.
\]
Exponential convergence makes the integral finite. Differentiating the semigroup and integrating gives \(Qh=-g\), while invariance gives \(\pi(h)=0\). This is the same centered Green operator developed in Chapter 72. In a finite-dimensional formalization, one can instead prove invertibility on the centered subspace and avoid improper integrals in the uniqueness argument.

The centering condition is essential. If one tries to solve \(-Qh=f\) when \(\pi(f)\ne0\), applying π to both sides yields \(0=\pi(f)\), a contradiction. In Lean, this obstruction is a useful lemma: invariance of π and the generator identity immediately show that every element in the range of Q has π-mean zero.

## 3. The martingale decomposition

For any function h, the generator martingale is
\[
  M_t^h=h(X_t)-h(X_0)-\int_0^t Qh(X_s)\,ds.
\]
With \(Qh=-g\), rearrangement gives
\[
  A_T=M_T^h-\bigl(h(X_T)-h(X_0)\bigr).
\]
The additive functional is therefore a martingale plus a boundary term with the indicated sign. Since h is bounded, \(|h(X_T)-h(X_0)|\leq2\lVert h\rVert_\infty\). After division by \(\sqrt T\), this term vanishes uniformly in the path.

This identity is the heart of the method. The endpoint correction contains the dependence between distant observations in a compact form, while the martingale has orthogonal increments. The decomposition does not say that \(g(X_t)\) itself is a martingale difference; it says that after correcting by the potential h, its accumulated drift becomes one.

The sign can be checked directly. From the martingale definition,
\[
  M_T^h=h(X_T)-h(X_0)+\int_0^T g(X_s)\,ds.
\]
Hence the integral equals M minus the endpoint difference. This elementary check prevents a frequent error when switching between conventions \(Qh=g\) and \(-Qh=g\).

## 4. Carré du champ and predictable variation

For functions h and k, define the generator carré du champ by
\[
  \Gamma_Q(h,k)(i)=\sum_{j\ne i}q(i,j)
       (h(j)-h(i))(k(j)-k(i)),
\]
and write \(\Gamma_Q(h)=\Gamma_Q(h,h)\). The diagonal term can be included because its increment is zero. Nonnegative off-diagonal rates imply \(\Gamma_Q(h)(i)\geq0\).

The predictable quadratic variation of \(M^h\) is
\[
  \langle M^h\rangle_T=\int_0^T\Gamma_Q(h)(X_s)\,ds.
\]
Each jump from i to j changes the martingale by \(h(j)-h(i)\); the conditional jump intensity is \(q(i,j)\). Summing rate times squared jump size gives Γ, and integrating the instantaneous rate gives the bracket. This local calculation explains why the generator representation is especially useful for formalization: a path-level quadratic-variation theorem can be reduced to a finite sum at each state.

The ergodic theorem now yields
\[
  \frac1T\langle M^h\rangle_T\longrightarrow\pi(\Gamma_Q(h))
  \quad\text{almost surely}.
\]
For a finite chain, h and all jump sizes are bounded. The martingale Lindeberg condition follows, so the martingale central limit theorem applies with variance \(\sigma_f^2=\pi(\Gamma_Q(h))\).

There is also a uniform integrability estimate behind this argument. If \(\lambda_* = \max_i\sum_{j\ne i}q(i,j)\), then \(\Gamma_Q(h)(i)\leq4\lambda_*\lVert h\rVert_\infty^2\). Thus the bracket grows at most linearly in time, and each martingale jump has magnitude at most \(2\lVert h\rVert_\infty\). These bounds make square integrability and the Lindeberg condition transparent. They also give explicit finite-time variance bounds before taking the limit.

Uniformization offers a discrete-time way to inspect the same local quantity. For \(\Lambda\geq\lambda_*\), put \(P=I+Q/\Lambda\). Then
\[
  \Gamma_Q(h)(i)=\Lambda\left(\operatorname{Var}_{P(i,\cdot)}(h)
                   +(Ph(i)-h(i))^2\right).
\]
The second term records the drift caused by inserting self-transitions into the Poisson clock. Omitting it would confuse the predictable variation per unit continuous time with the conditional variance of one uniformized step.

## 5. The asymptotic variance identities

Using invariance, \(\pi(Q(h^2))=0\). The pointwise identity
\[
  \Gamma_Q(h)=Q(h^2)-2h\,Qh
\]
therefore gives
\[
  \sigma_f^2=\pi(\Gamma_Q(h))=2\pi(hg).
\]
The right side need not look nonnegative for an arbitrary pair of functions, but here it equals the mean of the pointwise nonnegative function Γ.

When the chain is stationary, the covariance representation is
\[
  \sigma_f^2=2\int_0^\infty\operatorname{Cov}_\pi
       (f(X_0),f(X_t))\,dt.
\]
Indeed, \(h=\int_0^\infty P_tg\,dt\), so \(\pi(hg)\) is the one-sided covariance integral. The factor 2 comes from the two halves of the time square in the variance of \(\int_0^Tg(X_s)ds\). The integral is finite by exponential mixing. This is the continuous-time Green–Kubo formula.

The covariance formula is intuitive but can be analytically awkward: it requires controlling a two-time integral and its long-time tail. The carré-du-champ expression is local and finite-state. A strong formal proof can establish the local identity first and derive the covariance representation as a separate corollary using semigroup convergence.

### Reversible spectral check

If Q is reversible, choose an orthonormal eigenbasis for the π-weighted inner product. The constant eigenvector has eigenvalue zero; write the centered observable as \(g=\sum_{k\geq1}c_k\phi_k\), where \(-Q\phi_k=\lambda_k\phi_k\) and \(\lambda_k>0\). Then \(h=\sum_{k\geq1}(c_k/\lambda_k)\phi_k\), and
\[
  \sigma_f^2=2\langle g,h\rangle_\pi
       =2\sum_{k\geq1}\frac{c_k^2}{\lambda_k}.
\]
Slow modes with small λ contribute most strongly to long-run variance. This calculation also shows why a spectral gap gives an upper bound: if every nonzero λ is at least γ, then \(\sigma_f^2\leq2\pi(g^2)/\gamma\). This bound is a consistency check against Chapter 60’s mixing estimates; it is not available from an eigenbasis argument for a general non-normal generator.

The variance can vanish only when g is identically zero. Indeed, if \(\pi(\Gamma_Q(h))=0\), positivity of π and nonnegativity of every rate-weighted square force h to agree across every positive-rate edge. Irreducibility makes h constant on the state space; the centering condition gives h=0 and the Poisson equation then gives g=0. Thus every nonconstant observable of a finite irreducible chain has a strictly positive asymptotic variance.

## 6. Worked example: the two-state chain

Let the rates be \(0\to1\) at a and \(1\to0\) at b, with both positive. Take \(f=\mathbf1_{\{1\}}\), so \(\mu=a/(a+b)\) and \(g=(-a/(a+b),b/(a+b))\). Set \(s=a+b\). The equation \(-Qh=g\), together with \(\pi(h)=0\), gives
\[
  h(0)=-\frac{a}{s^2},\qquad h(1)=\frac{b}{s^2}.
\]
The jump difference is \(h(1)-h(0)=1/s\). Thus \(\Gamma_Q(h)(0)=a/s^2\) and \(\Gamma_Q(h)(1)=b/s^2\). Averaging against \(\pi=(b/s,a/s)\) gives
\[
  \sigma_f^2=\pi(\Gamma_Q(h))=\frac{2ab}{(a+b)^3}.
\]
This agrees with the cycle calculation in Chapter 73. Agreement between the Poisson, martingale, covariance, and regenerative formulas is a strong consistency check on rates and normalizations.

## 7. Worked example: a directed cycle

Consider the non-reversible chain on \(\{0,1,2\}\) that jumps from i to i+1 modulo 3 at rate c. Its stationary law is uniform. For \(f=\mathbf1_{\{0\}}\), the centered Poisson equation and centering condition yield
\[
  h(0)=\frac1{3c},\qquad h(1)=-\frac1{3c},\qquad h(2)=0.
\]
The three directed jump differences are \(-2/(3c),1/(3c),1/(3c)\). Therefore
\[
  \pi(\Gamma_Q(h))=\frac c3\left(\frac4{9c^2}+\frac1{9c^2}
       +\frac1{9c^2}\right)=\frac2{9c}.
\]
No detailed-balance argument is used. Reversibility can simplify the Poisson equation through self-adjoint spectral theory, but the martingale variance formula works for this directed circulation as well.

## 8. Several observables at once

For centered observables \(g_1,\ldots,g_m\), solve \(-Qh_r=g_r\) with \(\pi(h_r)=0\). The vector of additive functionals has a multivariate martingale decomposition. Its asymptotic covariance matrix has entries
\[
  \Sigma_{rs}=\pi(\Gamma_Q(h_r,h_s)).
\]
At each state, Γ is a sum of rate-weighted products of jump increments. Consequently Σ is positive semidefinite, since for coefficients c_r the quadratic form equals \(\pi(\Gamma_Q(\sum_rc_rh_r))\geq0\). The multivariate martingale central limit theorem gives the joint Gaussian limit.

This formulation is valuable for simultaneous estimation: one matrix describes the asymptotic errors and correlations of several statistics. It also gives an algebraic positivity proof that avoids expanding a covariance matrix into pairwise time integrals. For dependent samples, off-diagonal entries need not vanish even when the observables are pointwise orthogonal under π.

For a scalar observable, the limit theorem gives the large-T approximation \(\int_0^T f(X_t)dt\approx T\mu+\sqrt{T\sigma_f^2}\,Z\), with Z standard normal. Equivalently, the time-average standard error is approximately \(\sigma_f/\sqrt T\). This approximation is useful only after the chain has reached its long-run regime and T is large relative to slow mixing modes. In a formal development, the theorem should remain an asymptotic statement; a finite-sample confidence guarantee needs additional quantitative mixing or concentration bounds.

## 9. Relation to discrete-time chains

For a discrete transition matrix P, the analogous equation is \((I-P)h=g\), and the martingale is assembled from increments \(h(X_{n+1})-Ph(X_n)\). Its conditional variance is \(Ph^2-(Ph)^2\), rather than the continuous-time rate sum used above. The two formulas reflect different clocks: a discrete chain takes one transition per step, while a continuous-time chain has random holding times and rate-weighted jumps.

The centering and kernel issues are shared. Constants lie in the kernel of \(I-P\), and one solves on the π-centered subspace. For periodic chains, the Poisson equation can still be solvable for centered functions even though pointwise convergence \(P^n f\to\pi(f)\) fails. The martingale method needs the Poisson solution and an ergodic theorem for its bracket, not necessarily mixing at every discrete time.

## 10. Formalization architecture

Keep the development in four layers:

1. Prove that the centered subspace is invariant under Q and that \(-Q\) is invertible there.
2. Establish the Poisson equation and its normalization independently of sample paths.
3. Apply the generator-martingale theorem to h and identify the bracket with the integral of Γ.
4. Apply an ergodic theorem and a martingale central limit theorem, then remove the bounded endpoint correction.

The dependency structure is:

```text
invariant law + finite irreducibility ──> centered Poisson solution
                                                   │
                                                   v
generator martingale ──> carré du champ bracket ──> variance limit
                                                   │
                                                   v
                                      martingale central limit theorem
                                                   │
                                                   v
                                 additive-functional central limit theorem
```

For finite state spaces, express Γ as a finite sum over destinations. Prove nonnegativity from rate assumptions and prove \(\pi(\Gamma_Q(h))=2\pi(hg)\) by expanding the generator applied to \(h^2\). Keeping this identity at the function level avoids matrix-index bookkeeping in later applications.

The centered linear system can be solved in several equivalent ways. Add the normalization row \(\pi(h)=0\) to a redundant generator system, restrict Q to a basis of the centered subspace, or impose one coordinate and subtract the resulting mean afterward. The subspace approach gives the cleanest uniqueness statement; the augmented matrix can be more convenient for computation. Whichever representation is used, prove that the resulting h satisfies both the generator equation and the normalization before invoking the probabilistic theorem.

When the state type is abstractly finite, express all sums through its finite-enumeration interface and state nonnegativity only for off-diagonal rates. Diagonal entries are determined by the zero-row-sum condition. This representation makes the proof robust under a change of state labels and keeps the stochastic assumptions visible at the boundary of the linear-algebra layer.

The final theorem should expose its dependencies: irreducibility, finite state space, bounded observable, generator-martingale validity, the ergodic theorem, and the martingale central limit theorem. If some are packaged in a structure, document which fields supply path construction and which supply limit laws. This prevents a purely algebraic matrix result from being mistaken for a theorem about sample paths.

## 11. Common failure modes

### The observable is not centered

The Poisson equation for Q has a solution only when the right side has zero stationary mean. Replace f by \(f-\pi(f)\) before invoking invertibility.

### A normalization is omitted

Solutions differ by constants. Impose \(\pi(h)=0\) to obtain uniqueness and stable downstream statements.

### The sign convention changes mid-proof

With \(-Qh=g\), the additive functional equals the martingale minus the endpoint increment. Derive this identity from the martingale definition before simplifying.

### The bracket is confused with realized squared increments

The predictable bracket integrates rates times squared jump sizes. A pathwise sum of squared jumps is a different process, though it has the same compensator.

### Reversibility is assumed unnecessarily

The carré-du-champ and martingale arguments require invariance and finite-state irreducibility, not detailed balance. Self-adjoint spectral tools are an optional strengthening.

### A covariance integral is used without a tail bound

Exponential mixing in the finite irreducible case makes the Green–Kubo integral convergent. State this before exchanging limits and integrals.

## 12. Exercises

1. Show that every function in the range of Q has π-mean zero.
2. Prove uniqueness of the centered solution to \(-Qh=g\).
3. Derive the martingale decomposition and verify its endpoint sign.
4. Expand \(Q(h^2)-2hQh\) into the rate sum defining Γ.
5. Derive the two-state Poisson solution and its asymptotic variance.
6. Verify the directed three-cycle calculation without using reversibility.
7. Prove that \(\pi(\Gamma_Q(h))=2\pi(hg)\) for a centered Poisson solution.
8. Derive the Green–Kubo formula from the semigroup representation of h.
9. Define a cross carré du champ and prove the covariance matrix is positive semidefinite.
10. Compare the continuous-time bracket with the conditional variance in the discrete-time martingale decomposition.
11. List the probabilistic assumptions needed after the finite-dimensional Poisson equation is solved.

## Summary

The centered Poisson equation turns an additive functional into a martingale plus a bounded endpoint term. Its predictable bracket is the time integral of the carré du champ, whose stationary mean is the asymptotic variance. This yields a central limit theorem and equivalent Green–Kubo covariance formulas, including for non-reversible finite chains. In Lean, separate invertibility on the centered subspace, generator martingales, bracket identities, ergodic convergence, and the martingale limit theorem.

## Further reading

- Chapters 58–60 and 69 for generator martingales, semigroups, spectral methods, and Poisson equations.
- Chapter 72 for the centered Green operator and resolvent interpretation.
- Chapter 73 for the independent-cycle route to stationary laws and fluctuation limits.

## 13. Lean formalization: carré du champ and asymptotic variance

We specialize to the symmetric two-state chain with jump rate one in either direction. Its invariant law is uniform. For the centered observable `g = (-1, 1)`, the centered Poisson solution of `-Qh = g` is `h = (-1/2, 1/2)`. We verify the Poisson equation and the finite-state carré-du-champ identity, then compute both expressions for the asymptotic variance: `π(Γ(h))` and `2π(hg)`. They agree and equal one.

The original integer-valued centered example is preserved.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def additiveIncrement : State → Int := fun s => if s = zero then -1 else 1

theorem centeredAdditiveFunctional :
    expectationNumerator uniformWeight additiveIncrement = 0 := by decide
```

The pointwise identity below is stated for every observable on the two-state space. The diagonal generator term contributes zero to the carré du champ because its increment is zero.

```lean
def symmetricGenerator (i j : State) : ℚ := if i = j then -1 else 1

def symmetricAction (f : State → ℚ) (i : State) : ℚ :=
  symmetricGenerator i zero * f zero + symmetricGenerator i one * f one

def carreDuChamp (f : State → ℚ) (i : State) : ℚ :=
  (f zero - f i) ^ 2 + (f one - f i) ^ 2

theorem carreDuChamp_identity (f : State → ℚ) (i : State) :
    carreDuChamp f i =
      symmetricAction (fun j => f j ^ 2) i -
        2 * f i * symmetricAction f i := by
  fin_cases i <;>
    simp [carreDuChamp, symmetricAction, symmetricGenerator, zero, one] <;>
    ring

theorem carreDuChamp_nonnegative (f : State → ℚ) (i : State) :
    0 ≤ carreDuChamp f i := by
  unfold carreDuChamp
  positivity

def twoStateCenteredObservable (i : State) : ℚ :=
  if i = zero then -1 else 1

def twoStatePoissonSolution (i : State) : ℚ :=
  if i = zero then -(1 / 2) else 1 / 2

def uniformStateMean (f : State → ℚ) : ℚ := (f zero + f one) / 2

theorem twoState_observable_centered :
    uniformStateMean twoStateCenteredObservable = 0 := by
  norm_num [uniformStateMean, twoStateCenteredObservable, zero, one]

theorem twoState_poisson_at_zero :
    symmetricAction twoStatePoissonSolution zero =
      -twoStateCenteredObservable zero := by
  norm_num [symmetricAction, symmetricGenerator, twoStatePoissonSolution,
    twoStateCenteredObservable, zero, one]

theorem twoState_poisson_at_one :
    symmetricAction twoStatePoissonSolution one =
      -twoStateCenteredObservable one := by
  norm_num [symmetricAction, symmetricGenerator, twoStatePoissonSolution,
    twoStateCenteredObservable, zero, one]

def bracketVariance : ℚ :=
  uniformStateMean (fun i => carreDuChamp twoStatePoissonSolution i)

def poissonVariance : ℚ :=
  2 * uniformStateMean
    (fun i => twoStatePoissonSolution i * twoStateCenteredObservable i)

theorem twoState_asymptotic_variance_identity :
    bracketVariance = poissonVariance := by
  norm_num [bracketVariance, poissonVariance, uniformStateMean,
    carreDuChamp, twoStatePoissonSolution, twoStateCenteredObservable,
    zero, one]

theorem twoState_asymptotic_variance_value : bracketVariance = 1 := by
  norm_num [bracketVariance, uniformStateMean, carreDuChamp,
    twoStatePoissonSolution, zero, one]
```

The general carré-du-champ identity is a finite algebraic consequence of the generator definition. The specialized calculation checks the centering, Poisson sign convention, and variance normalization in one place. The martingale decomposition and central limit theorem still require path and probability arguments; the Lean block verifies their finite-state algebraic inputs.
