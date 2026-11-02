# Chapter 75 — Functional Central Limit Theorems

> **Audience.** This chapter assumes the martingale approximation and asymptotic variance formulas of Chapter 74. It lifts the scalar central limit theorem to a path-level Brownian limit for additive functionals.

The central limit theorem describes the error in one long-time average. A functional central limit theorem describes the errors over an entire range of times at once. As the observation horizon grows, the rescaled path of accumulated rewards approaches Brownian motion. This limit captures correlations between estimates at different times and supports sequential confidence bands, stopping rules, and diffusion approximations.

For finite irreducible continuous-time chains, the proof follows a clean sequence. Solve the centered Poisson equation, replace the additive functional by a martingale with a bounded endpoint correction, show its rescaled bracket converges to a linear function, then apply a martingale invariance principle. The formalization challenge is to preserve the time parameter and path topology throughout these steps.

## Learning objectives

By the end of the chapter, you should be able to:

- state the functional central limit theorem for a finite irreducible chain;
- derive uniform-on-compact convergence of the rescaled bracket;
- explain the role of jump-size control in tightness and Lindeberg conditions;
- extend the result to vector-valued observables;
- distinguish path-level convergence from convergence at one time;
- organize the formal proof around path spaces and martingale interfaces.

## 1. From a scalar limit to a path limit

Let \((X_t)\) be a finite irreducible continuous-time Markov chain with generator Q and stationary distribution π. Let \(f:S\to\mathbb R\), set \(\mu=\pi(f)\), and write \(g=f-\mu\mathbf1\). Define the rescaled additive-functional path
\[
  Z_T(t)=\frac1{\sqrt T}\int_0^{Tt}g(X_s)\,ds,\qquad t\geq0.
\]
For each fixed t>0, Chapter 74’s central limit theorem implies \(Z_T(t)\) converges in distribution to a centered normal random variable with variance \(t\sigma_f^2\). The functional theorem strengthens this collection of one-time statements to
\[
  Z_T\Rightarrow \sigma_f B
  \quad\text{in }D([0,\infty),\mathbb R),
\]
where B is standard Brownian motion and D is the space of right-continuous paths with left limits, equipped with the Skorokhod J1 topology.

The process \(Z_T\) itself is continuous: it is the integral of a bounded, piecewise-constant path. The martingale approximation used in the proof has jumps, but those jumps become small after division by \(\sqrt T\). The limiting Brownian path is continuous, so the endpoint correction can be discarded uniformly on compact time intervals.

The variance \(\sigma_f^2\) is the same quantity as in Chapter 74:
\[
  \sigma_f^2=\pi(\Gamma_Q(h)),
  \qquad -Qh=g,\quad \pi(h)=0.
\]
At t=1, the functional limit recovers the ordinary central limit theorem. The path statement contains more information because the limiting covariance is \(\operatorname{Cov}(\sigma_fB_s,\sigma_fB_t)=\sigma_f^2\min(s,t)\).

## 2. Martingale decomposition at every time

Let h be the centered Poisson solution and \(M^h\) the generator martingale. For every t,
\[
  Z_T(t)=\frac{M^h_{Tt}}{\sqrt T}
       -\frac{h(X_{Tt})-h(X_0)}{\sqrt T}.
\]
Because h is bounded on a finite state space,
\[
  \sup_{0\leq t\leq K}
  \frac{|h(X_{Tt})-h(X_0)|}{\sqrt T}
  \leq\frac{2\lVert h\rVert_\infty}{\sqrt T}
  \longrightarrow0
\]
for every finite K, with no probability estimate required. Thus the functional theorem reduces to the martingale process \(T^{-1/2}M^h_{Tt}\).

The supremum matters. A pointwise bound for each fixed t would not by itself justify deleting a whole path-valued error. Boundedness supplies a deterministic estimate valid simultaneously at every time, which is stronger and simpler than a union bound over a time grid.

The same argument works for any initial distribution. The centered Poisson equation uses the invariant π, while boundedness of h controls the initial and terminal states regardless of how the chain starts. Ergodicity is needed for the bracket limit, not for the algebraic decomposition.

## 3. Bracket convergence uniformly in time

The predictable quadratic variation of \(M^h\) is
\[
  \langle M^h\rangle_u=\int_0^u\Gamma_Q(h)(X_s)\,ds.
\]
The rescaled bracket at accelerated time is
\[
  V_T(t)=\frac1T\langle M^h\rangle_{Tt}
       =\frac1T\int_0^{Tt}\Gamma_Q(h)(X_s)\,ds.
\]
The ergodic theorem gives \(u^{-1}\int_0^u\Gamma_Q(h)(X_s)\,ds\to\sigma_f^2\). We need the stronger compact-uniform statement
\[
  \sup_{0\leq t\leq K}|V_T(t)-t\sigma_f^2|\longrightarrow0
  \quad\text{almost surely}.
\]

To see why the scalar ergodic theorem suffices, define
\[
  F(u)=\int_0^u(\Gamma_Q(h)(X_s)-\sigma_f^2)\,ds.
\]
Then \(F(u)/u\to0\). Given \(\varepsilon>0\), choose U so that \(|F(u)|\leq\varepsilon u\) for \(u\geq U\). On \(U\leq u\leq TK\), this bounds \(|F(u)|/T\) by \(\varepsilon K\). On \(0\leq u\leq U\), boundedness of Γ gives a fixed bound divided by T. Taking T large and then ε small proves compact-uniform convergence. This detail upgrades convergence at a single t to the bracket hypothesis needed for the martingale functional limit theorem.

If the chain starts from a deterministic state rather than stationarity, the same ergodic theorem holds for finite irreducible chains. One can alternatively separate the initial transient interval; its length is negligible compared with T, while the bracket integrand is bounded.

## 4. Vanishing jumps and tightness

At a jump from i to j, \(M^h\) jumps by \(h(j)-h(i)\). Hence
\[
  \sup_{u\geq0}|\Delta M^h_u|
  \leq2\lVert h\rVert_\infty,
  \qquad
  \sup_{t\geq0}|\Delta(T^{-1/2}M^h_{Tt})|
  \leq\frac{2\lVert h\rVert_\infty}{\sqrt T}\to0.
\]
The scaled jumps vanish deterministically. This verifies the martingale Lindeberg condition and rules out a jump component in the limit.

For path-space convergence, bracket convergence controls accumulated variance, while jump control rules out large individual increments. Together they imply tightness of the martingale sequence in D and identify every subsequential limit as a continuous martingale with bracket \(t\sigma_f^2\). Lévy’s characterization then identifies that limit as Brownian motion scaled by σ. If \(\sigma_f^2=0\), the limit is the constant zero path; the theorem includes this degenerate case.

One may formulate a martingale functional central limit theorem using predictable brackets, optional quadratic variations, or conditional variance arrays. These versions have different hypotheses. For the finite-state jump chain, the predictable bracket is explicit and bounded per unit time, so it is usually the most direct interface. Do not mix a theorem stated with one quadratic-variation convention with a proof of another without supplying the compensator identity.

## 5. Worked example: the two-state chain

Let state 0 jump to 1 at rate a and state 1 return at rate b, with \(a,b>0\). For \(f=\mathbf1_{\{1\}}\), the stationary mean is \(a/(a+b)\), and Chapter 74 gives
\[
  \sigma_f^2=\frac{2ab}{(a+b)^3}.
\]
The functional limit is therefore
\[
  \frac1{\sqrt T}\int_0^{Tt}
     \left(\mathbf1_{\{X_s=1\}}-\frac a{a+b}\right)ds
  \Rightarrow\sqrt{\frac{2ab}{(a+b)^3}}\,B_t.
\]
At a fixed t, the variance is \(2ab\,t/(a+b)^3\). For two times s≤t, the limiting covariance is \(2ab\,s/(a+b)^3\). The minimum-time dependence is a diagnostic of Brownian scaling; treating estimates at different horizons as independent would give the wrong joint law.

The same limit follows from regenerative cycles. Each cycle contributes a centered reward, and the number of completed cycles by time \(Tt\) grows at rate \(Tt/\mathbb E[C]\). The renewal-reward central limit theorem must be strengthened to a process-level renewal theorem to obtain the whole path. The martingale proof avoids tracking the random cycle count and makes the covariance structure immediate.

## 6. Worked example: a directed three-cycle

Consider the chain \(0\to1\to2\to0\) with common rate \(c>0\) and observable \(f=\mathbf1_{\{0\}}\). The stationary law is uniform, and Chapter 74 computed \(\sigma_f^2=2/(9c)\). Thus the centered occupation path converges to \(\sqrt{2/(9c)}B_t\), despite the chain’s non-reversibility.

This example illustrates that the functional limit theorem does not require a spectral theorem for self-adjoint operators. The Poisson equation, martingale bracket, and ergodic theorem work in the directed setting. Reversibility is useful for deriving bounds on σ or comparing modes, but it is not part of the invariance-principle hypotheses.

## 7. Several observables and Brownian covariance

For centered functions \(g_1,\ldots,g_m\), let \(-Qh_r=g_r\) with \(\pi(h_r)=0\). The vector additive functional converges to an m-dimensional Brownian motion with covariance matrix
\[
  \Sigma_{rs}=\pi(\Gamma_Q(h_r,h_s)).
\]
For any vector c, \(c^T\Sigma c=\pi(\Gamma_Q(\sum_rc_rh_r))\geq0\), so Σ is positive semidefinite. The limiting covariance at times s,t is \((s\wedge t)\Sigma\).

This joint limit is stronger than applying the scalar theorem separately to each observable. Separate scalar convergence does not determine cross-covariances or establish joint tightness. The vector martingale provides both in one step: its predictable bracket is a matrix-valued integral, and the ergodic theorem applies to each of its finitely many entries.

Linear transformations are compatible with the limit. If \(L:\mathbb R^m\to\mathbb R^k\) is linear, then the transformed additive functional converges to Brownian motion with covariance \(L\Sigma L^T\). In formalization, this follows from the continuous mapping theorem once the vector-valued path convergence is available; it should not require a second martingale argument.

## 8. Applications of the path-level limit

The functional theorem supports statistics that depend on an entire trajectory. For example, it describes the leading fluctuations of a cumulative reward curve, not just its endpoint. It also gives joint limits for partial averages at times \(t_1,\ldots,t_k\), with covariance \((t_i\wedge t_j)\sigma_f^2\). This dependence is essential when choosing a stopping horizon based on the observed path.

The limit can be combined with a continuous functional of the path. For instance, the running maximum of the rescaled centered integral converges to the running maximum of \(\sigma_f B\), provided the chosen path functional is continuous at Brownian paths under the selected topology. Such applications require a separate continuous-mapping argument; they do not follow from the one-time central limit theorem alone.

The approximation is asymptotic rather than a finite-sample guarantee. To obtain explicit error bounds for a given T, one needs quantitative mixing or martingale approximation estimates, such as a spectral gap or coupling bound. The invariance principle identifies the limiting law and covariance, while concentration inequalities quantify the rate at which a finite chain approaches that limit.

For example, the maximum deviation over a time window satisfies
\[
  \sup_{0\leq t\leq K}|Z_T(t)|
  \Rightarrow \sigma_f\sup_{0\leq t\leq K}|B_t|.
\]
This can calibrate a sequential alarm that monitors cumulative excess reward. Such a statement would be inaccessible from the single-time central limit theorem, since a maximum depends on the full dependence structure across the window. The limiting distribution is also not the distribution of \(|Z_T(K)|\); it accounts for the chance that the path crossed a threshold earlier.

### Stopping rules and continuity points

Once path convergence is proved, continuous-mapping arguments give limits for many trajectory statistics. Evaluation at a fixed time is continuous at every continuous limiting path under the J1 topology. So are the running maximum and integration over a fixed compact interval. Brownian continuity therefore lets these statistics inherit their corresponding Brownian limits.

First-passage times require more care. The map sending a path to the first time it crosses a level can be discontinuous when a path merely touches the level, crosses tangentially, or has a flat segment at the threshold. A proof about a threshold stopping time needs conditions ensuring continuity at almost every Brownian path, or a separate first-passage theorem. One cannot infer a valid stopping-time limit solely from the deterministic-time invariance principle.

The same warning applies to substituting a random horizon \(\tau_T\) into \(Z_T(t)\). If \(\tau_T\) is itself data-dependent, establish joint convergence of the path and horizon and verify continuity of evaluation at the limiting pair. For sequential procedures this is a meaningful extra theorem, not a notational change. The formal development should state whether a result concerns fixed times, continuous path functionals, or random times.

The path topology also determines what “uniformly close” means. J1 convergence permits a small change of time when comparing jumps, whereas uniform convergence compares values at the same clock time. When the limiting path is continuous, J1 convergence is strong enough for the standard continuous-mapping results used above, but a formal proof should still invoke the theorem for the named topology rather than silently replacing one metric by another. This distinction becomes more important in models whose limiting process has jumps.

## 9. Formalization architecture

Organize the theorem around the objects that change with T:

1. a path-valued rescaled additive functional \(Z_T\);
2. a path-valued rescaled martingale \(M_T\);
3. a predictable bracket process \(V_T\);
4. a martingale functional limit theorem in a specified path topology;
5. a uniform endpoint estimate transferring the limit from \(M_T\) to \(Z_T\).

The logical flow is:

```text
centered Poisson solution ──> additive functional = martingale + endpoint
                                              │
                                              v
bounded jumps ──> Lindeberg     bracket ergodic theorem ──> linear bracket
          \                              │                         /
           └─────────────────────────────┴────────────────────────/
                                         v
                           martingale invariance principle
                                         │
                                         v
                         Brownian path limit for rewards
```

Do not encode the entire conclusion as a single opaque theorem. First prove the endpoint bound in the supremum norm on each compact interval. Separately prove compact-uniform bracket convergence. Then supply these facts to the martingale theorem, whose conclusion names the Skorokhod topology. Finally, use a path-space Slutsky theorem to transfer convergence across a uniformly vanishing error.

For vector observables, define the matrix bracket and prove entrywise convergence. Positive semidefiniteness can be derived by testing against a vector and reducing to the scalar carré du champ. This avoids a separate matrix positivity proof and makes the covariance argument reusable for every finite output dimension.

The formal interface should expose whether a process is adapted, càdlàg, square-integrable, and a martingale; whether its bracket is predictable; and which filtration is used. A path with the right distribution but no adaptedness data is insufficient for the martingale limit theorem. Likewise, ordinary pointwise convergence of brackets is weaker than the compact-uniform or in-probability condition required by the chosen theorem.

## 10. Common failure modes

### Only one-time convergence is proved

Convergence of \(Z_T(t)\) for each fixed t does not imply convergence of the path. Establish tightness and identify the finite-dimensional laws, or invoke a functional martingale theorem with its full hypotheses.

### Bracket convergence is shown only at t=1

The path theorem needs convergence over compact time intervals. Derive uniform convergence from the ergodic theorem and boundedness of the bracket integrand.

### The endpoint correction is discarded pointwise

Use the deterministic supremum bound for h. This proves the correction vanishes as a path, not just at one selected time.

### Jump sizes are ignored

Bracket convergence alone does not exclude large jumps in the limit. Verify the scaled jumps vanish or check the appropriate Lindeberg condition.

### The topology is omitted

State the path space and topology. Here the natural result is in Skorokhod J1, with a continuous Brownian limit.

### Scalar limits are assembled into a vector limit informally

Prove a vector martingale theorem or establish joint tightness and covariance convergence. Marginal normal limits alone do not determine a joint law.

## 11. Exercises

1. Define \(Z_T\) and derive its martingale-plus-endpoint decomposition for every t.
2. Prove compact-uniform bracket convergence from the scalar ergodic theorem.
3. Show that the scaled martingale jumps are bounded by \(2\lVert h\rVert_\infty/\sqrt T\).
4. State the functional limit with the variance from Chapter 74 and verify its t=1 marginal.
5. Compute the joint limiting covariance at two times s and t.
6. Extend the bracket argument to a finite vector of observables.
7. Explain why convergence in distribution at rational times needs an additional tightness argument.
8. Identify where an initial distribution other than π enters the proof.
9. State a path-space Slutsky result that removes the endpoint correction.
10. Give a finite-time estimate that would be needed to turn the asymptotic theorem into a quantitative approximation.

## Summary

The functional central limit theorem sends the accelerated, centered reward path to Brownian motion. The Poisson equation supplies a martingale representation with a uniformly negligible endpoint term; the ergodic theorem yields compact-uniform convergence of its bracket; bounded jumps verify the martingale invariance principle. The same argument yields vector Brownian limits with covariance from the cross carré du champ. Formalization must track path topology, compact-time bracket convergence, adaptedness, and the jump condition.

## Further reading

- Chapter 74 for the centered Poisson equation, scalar martingale approximation, and asymptotic covariance.
- Chapters 58 and 60 for generator martingales, ergodicity, and spectral estimates.
- Chapter 73 for the regenerative route to long-time averages and scalar fluctuation limits.
