# Chapter 71 — Quasi-Stationary Laws and Doob Transforms

> **Audience.** This chapter assumes finite-state continuous-time chains, killing, Feynman–Kac semigroups, and finite-dimensional Perron–Frobenius theory. It studies the law of a chain conditioned on avoiding an absorbing event for a long time.

When a process can be killed or absorbed, its ordinary stationary distribution may be concentrated at the absorbing state. Yet practitioners often care about the transient dynamics before absorption: a population before extinction, a chemical system before a reaction threshold, or a chain before leaving a safe set. A quasi-stationary distribution (QSD) is stationary after conditioning on survival. A Doob h-transform converts the long-survival conditioned dynamics into an ordinary conservative Markov chain.

In finite state spaces, the theory reduces to positive eigenvectors of a subgenerator. This chapter develops that algebra, computes a two-state example, and connects the transformed chain’s invariant law to left and right Perron eigenvectors.

## Learning objectives

By the end of this chapter, you should be able to:

- define a killed finite-state generator and its survival semigroup;
- characterize a QSD as a positive left eigenvector;
- construct the Doob h-transform from a positive right eigenvector;
- identify the invariant law of the conditioned-to-survive process;
- calculate a two-state killing example explicitly;
- distinguish finite matrix eigenvector arguments from long-time conditional limits.

## 1. Killed chains and subgenerators

Let S be a finite set of transient states. A killed continuous-time chain has rates (q(i,j)\geq0) for distinct i,j in S and a killing rate κ(i)≥0 from i to a cemetery state outside S. Its subgenerator K on S is
\[
  K(i,j)=q(i,j)\quad(i\ne j),\qquad
  K(i,i)=-\sum_{j\ne i}q(i,j)-\kappa(i).
\]
Rows need not sum to zero: \(\sum_jK(i,j)=-\kappa(i)\). The substochastic matrix \(P_t=e^{tK}\) records transition probabilities that remain in S. The survival probability from initial law α is
\[
  \Pr_\alpha(T_{\partial}>t)=\alpha e^{tK}\mathbf1.
\]
Killing can also represent exiting a chosen domain, entering a forbidden set, or applying a Feynman–Kac weight that removes mass. Keep the cemetery state implicit in K or add it explicitly, but do not claim the restricted matrix itself is a conservative generator.

Assume the internal transition graph on S is irreducible and that killing is possible from at least one state. Because every state can reach a state with positive killing rate, eventual killing occurs with probability one. In finite dimension the survival probability decays exponentially at long times, governed by the eigenvalue of K with largest real part.

## 2. Quasi-stationary distributions

A probability row vector ν on S is a quasi-stationary distribution if conditioning on survival leaves the law unchanged:
\[
  \Pr_\nu(X_t=i\mid T_\partial>t)=\nu(i)
  \quad\text{for all }t\geq0.
\]
Since ν e^{tK} is the unnormalized surviving distribution, this condition is equivalent to
\[
  \nu e^{tK}=s(t)\nu
\]
for some survival function s(t). The semigroup law forces (s(t)=e^{-\lambda t}), and differentiation at zero gives
\[
  \nu K=-\lambda\nu.
\]
The scalar λ is the exponential decay rate of survival. Conversely, a nonnegative normalized left eigenvector for eigenvalue −λ yields a QSD whenever the associated survival factor is positive.

For an irreducible finite subgenerator with accessible killing, Perron–Frobenius theory gives a unique positive normalized left eigenvector for the spectral-abscissa eigenvalue −λ, with λ>0. This is the Yaglom limit: from any initial state, the conditional law given survival to time t converges to ν as t tends to infinity. The eigenvector identity proves the QSD property immediately; the convergence from arbitrary starts additionally uses dominance of the principal eigenvalue over the remaining spectrum.

Starting exactly from ν, the survival probability is \(e^{-\lambda t}\) at every time, not only asymptotically. Indeed, ν is normalized and \(\nu e^{tK}=e^{-\lambda t}\nu\), so multiplying by the all-ones vector gives the survival formula. This constant hazard at the level of the conditioned law is characteristic of a QSD; individual states may have different killing rates, but the conditional mixture maintains an exponential survival curve.

This distinction is important in formal proofs. The algebraic statement “a positive left eigenvector defines a QSD” is short. The asymptotic theorem “every initial law converges conditionally to the QSD” needs a spectral-gap or Perron asymptotic argument. Do not hide the second result inside the definition of quasi-stationarity.

## 3. The right eigenvector and the Doob transform

Let h:S→(0,∞) be a positive right eigenvector for the same principal eigenvalue:
\[
  Kh=-\lambda h.
\]
Define a new operator on observables by
\[
  (K^h f)(i)=\frac1{h(i)}K(hf)(i)+\lambda f(i).
\]
Since \(Kh=-\lambda h\), we have \(K^h\mathbf1=0\). Thus Kʰ is conservative. For i≠j its transition rate is
\[
  q^h(i,j)=q(i,j)\frac{h(j)}{h(i)}.
\]
The diagonal is the negative sum of these transformed rates. The killing has disappeared: the h-transform describes the chain conditioned to survive indefinitely in the limiting sense.

In matrix notation,
\[
  K^h=\operatorname{diag}(h)^{-1}K\operatorname{diag}(h)+\lambda I.
\]
The similarity transform preserves the shifted spectrum, moving the principal eigenvalue −λ to zero. This explains why the transformed semigroup is stochastic even though the original killed semigroup loses mass.

The transformed stationary law is
\[
  \pi^h(i)=\frac{\nu(i)h(i)}{\sum_j\nu(j)h(j)}.
\]
Indeed, multiplying ν by the transformed generator cancels the eigenvalue terms:
\[
  \nu\operatorname{diag}(h)K^h
   =\nu K\operatorname{diag}(h)+\lambda\nu\operatorname{diag}(h)=0.
\]
After normalization, πʰ is invariant. This law is generally not the QSD ν; the left eigenvector describes the distribution at a long surviving time, while the right eigenvector biases starting states by their future survival potential.

The eigenvectors also give an exact path likelihood ratio. On paths that remain in S until time t, the density of the h-transformed process relative to the original killed process is
\[
  \frac{d\mathbb P_i^h}{d\mathbb P_i^{\mathrm{killed}}}
      =e^{\lambda t}\frac{h(X_t)}{h(i)}.
\]
For a finite jump path, the rate ratios telescope to \(h(X_t)/h(i)\). The holding-time densities differ by the factor \(e^{\lambda t}\), because the h-transform increases the total internal jump rate by the eigenvalue correction. This identity is the basis for importance sampling of long-surviving paths. A formal proof can establish it for a fixed jump sequence first, then sum or integrate over path lengths and holding times.

## 4. Worked example: two transient states

Consider internal transitions \(1\rightleftarrows2\) at rate r in each direction. State 1 is killed at rate κ>0; state 2 has no direct killing. The subgenerator is
\[
  K=\begin{pmatrix}-(r+\kappa)&r\\r&-r\end{pmatrix}.
\]
Its principal eigenvalue is −λ, where
\[
  \lambda=\frac{2r+\kappa-\sqrt{\kappa^2+4r^2}}2>0.
\]
Because K is symmetric, left and right positive eigenvectors agree. Set \(h_1=1\); the first row of \(Kh=-\lambda h\) gives
\[
  h_2=\frac{r+\kappa-\lambda}{r}.
\]
The QSD is \(\nu\propto(1,h_2)\). The transformed rate from 1 to 2 is \(r h_2\), while from 2 to 1 it is \(r/h_2\). Its stationary law is proportional to \((1,h_2^2)\), exactly the coordinatewise product \(\nu_i h_i\).

When κ is small, survival conditioning only mildly favors state 2. As κ grows, a long-lived trajectory spends more time away from state 1, and the ratio h₂/h₁ increases. This example gives closed expressions for the decay rate, QSD, h-transform, and conditioned stationary law.

At \(\kappa=0\), the process is no longer killed; \(\lambda=0\) and the QSD reduces to the ordinary stationary distribution of the symmetric two-state chain. The formula varies continuously toward that limit, but theorem hypotheses for a killed chain should still require positive accessible killing when asserting \(\lambda>0\).

### A path with a killed endpoint

Take the three-vertex path \(0\leftrightarrow1\leftrightarrow2\) with edge rate r in both directions, and kill at the first visit to 2. The transient states are 0 and 1, with
\[
  K=\begin{pmatrix}-r&r\\r&-2r\end{pmatrix}.
\]
The principal decay rate is
\[
  \lambda=\frac{3r-\sqrt5\,r}{2},
\]
and a positive right eigenvector normalized by h(0)=1 has
\[
  h(1)=1-\lambda/r=\frac{\sqrt5-1}{2}.
\]
The left eigenvector is the same because K is symmetric. Consequently, the long-survival distribution on {0,1} is proportional to \((1,h(1))\), while the Q-process stationary law is proportional to \((1,h(1)^2)\).

Here h(0)>h(1): state 0 is farther from killing. The transformed process changes the rate from 0 to 1 by the factor h(1)/h(0), slowing movement toward the target, and changes the reverse rate by h(0)/h(1), favoring return to safety. The original chain is symmetric, but the conditioned dynamics are not.

## 5. Worked example: conditioning a finite random walk to avoid a target

Take a finite irreducible chain and choose a nonempty target set A. Kill the process at its first entry into A; then S is the complement of A and K is the generator restricted to S with rates into A included in the diagonal loss. When the induced internal graph on S is irreducible, the QSD describes the unique long-time distribution among trajectories that have not yet hit A. If removing A disconnects S, analyze the transient communicating classes and identify which class has the dominant survival eigenvalue before asserting uniqueness.

The positive right eigenfunction h measures relative survival potential. States with larger h are favored under the Doob transform because their future survival prospects are better. A transition from i to j is reweighted by h(j)/h(i). The transformed process remains inside S and has no killing. This is a principled way to simulate rare trajectories conditioned to avoid A, rather than rejecting paths that hit A.

For a path graph and a single target endpoint, the killed generator is tridiagonal. Its principal eigenpair can be characterized by a recurrence, allowing the methods of Chapter 63 to reappear: solve the interior eigenvalue equation with the killed boundary condition, then normalize the positive eigenvector. The stationary QSD is a left eigenvector, while the survival function h is a right eigenvector; reversible killed chains relate them by the stationary weights.

## 6. A finite-time conditioning identity

For a fixed horizon T, the chain conditioned on survival until T is generally time-inhomogeneous. If it is at state i at time t<T, the probability of moving to j over a short interval is biased by the chance of surviving the remaining horizon from j. Define
\[
  h_t(i)=\Pr_i(T_\partial>T-t)=(e^{(T-t)K}\mathbf1)(i).
\]
The time-dependent transformed off-diagonal rates are
\[
  q_t(i,j)=q(i,j)\frac{h_t(j)}{h_t(i)}.
\]
As \(T-t\) becomes large, the principal eigenvector asymptotic gives \(h_t(i)\approx e^{-\lambda(T-t)}h(i)\) up to a common factor. The finite-horizon rates then converge to the time-homogeneous Q-process rates \(q^h(i,j)\).

The complete conditioned transition kernel between times s and t is
\[
  P^{(T)}_{s,t}(i,j)
    =\frac{(e^{(t-s)K})(i,j)h_t(j)}{h_s(i)},
  \qquad 0\leq s\leq t\leq T.
\]
Its rows sum to one because the semigroup property gives (e^{(t-s)K}h_t=h_s). This identity is the time-inhomogeneous Doob transform at the kernel level; differentiating in t recovers the rate formula. It is often easier to formalize the kernel identity first, since it uses only matrix multiplication and positivity, and derive the infinitesimal generator afterward.

This distinction is useful computationally. Conditioning on survival to a known finite deadline uses a time-varying transform; conditioning on indefinite survival uses the principal h-transform. Replacing \(h_t\) with h at a short horizon can bias the finite-horizon conditioned law.

## 7. Relation to Feynman–Kac and rare-event tilting

Killing at rate κ(i) is equivalent to weighting paths by
\[
  \exp\left(-\int_0^t\kappa(X_s)\,ds\right).
\]
The corresponding Feynman–Kac operator is \(Q-\operatorname{diag}\kappa\), a subgenerator. Thus quasi-stationarity is a special spectral problem for a Feynman–Kac semigroup. Chapter 70’s tilted generators add a general potential; here the potential is nonpositive and represents survival loss.

The Doob transform is also the zero-variance ideal for importance sampling of rare survival events: it changes rates to favor paths that realize the conditioning while preserving a likelihood ratio. In practice h is unknown and must be approximated, but the exact transform identifies the target structure. A formal development can derive the path likelihood ratio from the changed jump rates and verify unbiasedness for a finite horizon.

With the paired normalization \(\nu h=1\), the principal spectral asymptotic has the rank-one form
\[
  e^{tK}=e^{-\lambda t}h\nu+R_t,
\]
where the remainder \(R_t\) decays faster in operator norm. It follows that survival from i is asymptotic to \(e^{-\lambda t}h(i)\), while the conditional endpoint law converges to ν. This expansion explains the eigenvectors’ distinct roles and yields the long-horizon conditioned kernel. In formalization, state a norm bound on \(R_t\) rather than only entrywise convergence; it composes well with matrix multiplication and uniform estimates over initial states.

## 8. Formalization architecture

The core definitions fit naturally in finite matrix language:

1. a subgenerator K with nonnegative off-diagonal entries and nonpositive row sums;
2. a positive left eigenvector ν and right eigenvector h for the same eigenvalue;
3. a proof that the eigenvalue is negative when killing is accessible;
4. the h-transformed matrix and its zero row sums;
5. the invariant vector ν·h for the transformed generator.

The main proof flow is:

```text
killed generator ──> principal left/right eigenvectors ──> QSD and survival rate
                                      │
                                      v
                            positive h-transform ──> conservative generator
                                      │
                                      v
                            stationary law proportional to ν·h
```

Finite-state Perron theory is the key dependency. If the library provides only spectral results for Hermitian matrices, the symmetric example can use that API, while the general nonreversible theorem needs a positive-matrix Perron result or a custom proof. A convenient reduction shifts K by a large scalar to a nonnegative irreducible matrix. The shift changes the eigenvalue but not the eigenvectors.

Keep the eigenvector normalizations separate: choose \(\sum_i\nu(i)=1\) for the QSD and scale h by \(\sum_i\nu(i)h(i)=1\). Then the transformed stationary law is simply \(\pi^h(i)=\nu(i)h(i)\). The h-transform is invariant under multiplying h by a positive scalar, so this paired normalization is often cleaner than fixing h at a reference state. Encoding that scale invariance explicitly avoids unnecessary equalities between arbitrarily normalized eigenvectors.

## 9. Common failure modes

### The killed subgenerator is called conservative

Its row sums are negative killing rates. Only the h-transform has zero row sums.

### A QSD is confused with the Q-process invariant law

The QSD is ν; the transformed stationary law is proportional to ν_i h_i.

### Left and right eigenvectors are interchanged

The QSD solves νK=−λν; the survival function solves Kh=−λh.

### The transformed diagonal is left unchanged

After transforming off-diagonal rates, reset the diagonal so rows sum to zero; equivalently use the full conjugation plus λI formula.

### A finite-horizon conditioning is treated as time-homogeneous

Its survival potential depends on remaining time. The principal h-transform is the long-horizon limit.

## 10. Exercises

1. Show that a normalized positive left eigenvector of K gives a QSD.
2. Derive the survival decay rate from the eigenvalue equation.
3. Prove that the Doob h-transform has zero row sums.
4. Verify that ν_i h_i is invariant for the transformed generator.
5. Compute the two-state killing example and check positivity of λ.
6. Derive the finite-horizon time-dependent rate formula.
7. Explain why the QSD and Q-process invariant law differ.
8. Relate killing at rate κ(i) to a Feynman–Kac potential.
9. Derive the likelihood ratio between the killed process and its h-transform on a finite path.
10. Identify Perron assumptions needed when the internal state graph is reducible.

## Summary

A finite killed chain has a subgenerator with nonpositive row sums. Its quasi-stationary law is a positive left eigenvector for the principal decay eigenvalue, while a positive right eigenvector defines a Doob h-transform with conservative rates. The transformed chain describes the long-survival conditioned dynamics, and its invariant law is proportional to the product of the left and right eigenvectors. Finite-time conditioning uses a time-dependent survival potential; the homogeneous Q-process emerges in the long-horizon limit.

## Further reading

- Chapters 59 and 70 for Feynman–Kac semigroups, killing, and tilted spectral problems.
- Chapters 68–69 for positive eigenvectors, stationary sensitivity, and finite-state response identities.
- [Mathlib’s finite matrix spectral theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html).
