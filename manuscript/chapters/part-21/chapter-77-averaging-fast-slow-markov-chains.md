# Chapter 77 — Averaging for Fast–Slow Markov Chains

> **Audience.** This chapter assumes finite-state continuous-time chains, generator martingales, Poisson equations, and diffusion approximations. It derives deterministic averaged dynamics and their leading Gaussian correction when a finite environment switches rapidly.

Many systems combine a slowly changing state with a rapidly switching environment. A queue may operate under changing service regimes; an epidemic may move through weather or policy states; a controller may switch modes much faster than the physical state evolves. On the slow time scale, the fast regime is often replaced by its stationary distribution. The resulting averaged model is simpler, but proving the replacement requires more than saying that the environment “mixes quickly.”

For a finite fast chain, a parameter-dependent Poisson equation turns the centered environmental drift into a small corrector plus a martingale. This gives a law-of-large-numbers averaging theorem. The martingale’s bracket then determines the Gaussian error around the averaged trajectory. The two conclusions use the same corrector but have different scales and proof obligations.

## Learning objectives

By the end of the chapter, you should be able to:

- define a slow process modulated by a fast finite-state chain;
- average its drift using the invariant law of the frozen fast generator;
- use a Poisson corrector to bound the integrated centered drift;
- derive the covariance of environmental fluctuations;
- distinguish environmental noise from population jump noise;
- formalize parameter-dependent Poisson equations and uniform estimates.

## 1. A finite-state fast environment

Let E be a finite set. For each slow state x in a compact set K, let \(Q_x\) be the generator of an irreducible chain on E, and let \(\pi_x\) be its unique invariant distribution. The fast environment \(Y^\varepsilon_t\) evolves with generator \(Q_x/\varepsilon\), where x is the current slow state and \(\varepsilon\downarrow0\) is the time-scale parameter.

For clarity, begin with a continuous slow variable satisfying
\[
  \frac{d}{dt}X^\varepsilon_t=b(X^\varepsilon_t,Y^\varepsilon_t),
  \qquad X^\varepsilon_0=x_0.
\]
Assume b is bounded and Lipschitz in x, and the slow path remains in K. The generator of the joint process, on a function \(\varphi(x,y)\) differentiable in x, is
\[
  \mathcal L^\varepsilon\varphi(x,y)
   =b(x,y)\cdot\nabla_x\varphi(x,y)
     +\frac1\varepsilon Q_x\varphi(x,\cdot)(y).
\]
The fast generator is “frozen” at the current slow state when taking its invariant law. The averaged drift is
\[
  \bar b(x)=\sum_{y\in E}\pi_x(y)b(x,y).
\]
The proposed deterministic limit solves \(\dot{\bar X}_t=\bar b(\bar X_t)\), with \(\bar X_0=x_0\).

The dependence of \(Q_x\) and \(\pi_x\) on x is essential. Averaging against one fixed stationary distribution is correct only when the fast chain itself does not depend on the slow state. In the state-dependent case, the environment equilibrates locally along the path.

## 2. The centered Poisson equation

For each x, define the centered drift
\[
  \widetilde b(x,y)=b(x,y)-\bar b(x).
\]
It has zero mean under the frozen invariant law: \(\sum_y\pi_x(y)\widetilde b(x,y)=0\). Solve the vector-valued Poisson equation coordinatewise:
\[
  Q_x h(x,\cdot)(y)=-\widetilde b(x,y),
  \qquad \sum_y\pi_x(y)h(x,y)=0.
\]
For each coordinate, irreducibility makes the kernel of \(Q_x\) the constants, and the centered subspace is its range. The normalization therefore gives a unique solution.

The formal theorem needs uniform control as x varies. A convenient assumption is a uniform spectral gap for \(Q_x\) on K together with sufficient regularity of the rates. This gives boundedness of h and, under smooth dependence of \(Q_x\) and b, bounded derivatives in x. Alternatively, state boundedness and Lipschitz regularity of h directly and prove it from the matrix equation in a separate lemma.

For finite E, one can represent the centered subspace using the constraint \(\pi_x(h)=0\), then invert \(Q_x\) on that subspace. Uniform invertibility over compact K is the key quantitative fact. It can follow from continuity of the matrix entries, irreducibility at each x, and compactness only if the smallest nonzero singular value stays away from zero; pointwise nonsingularity alone does not provide a uniform bound. When the stationary law is differentiated, differentiate both its equation \(\pi_xQ_x=0\) and its normalization. This yields a second normalized linear system rather than an informal derivative of an eigenvector.

The corrector h is not itself the averaged trajectory. It records the potential accumulated by the centered drift while the fast chain moves. In the scalar case, a state with persistently high drift is balanced by the fast chain’s return flow; h measures that imbalance through an inverse generator.

## 3. Why the environmental drift averages

Apply the joint generator martingale formula to \(h(X^\varepsilon_t,Y^\varepsilon_t)\). Since the slow coordinate has finite variation,
\[
  h(X^\varepsilon_t,Y^\varepsilon_t)-h(x_0,Y^\varepsilon_0)
   =\int_0^t b\cdot\nabla_x h\,ds
     -\frac1\varepsilon\int_0^t\widetilde b(X^\varepsilon_s,Y^\varepsilon_s)\,ds
     +M^\varepsilon_t.
\]
Rearranging gives
\[
  \int_0^t\widetilde b(X^\varepsilon_s,Y^\varepsilon_s)\,ds
   =\varepsilon\left[
       \int_0^t b\cdot\nabla_xh\,ds+M^\varepsilon_t
       -h(X^\varepsilon_t,Y^\varepsilon_t)+h(x_0,Y^\varepsilon_0)
     \right].
\]
If h and its slow derivative are bounded, the endpoint and drift terms on the right are order \(\varepsilon\). The martingale bracket grows at rate order \(1/\varepsilon\), so Doob’s inequality makes \(\varepsilon M^\varepsilon\) order \(\sqrt\varepsilon\) in probability on every fixed horizon. Consequently the time-integrated centered drift vanishes uniformly on compact intervals.

More explicitly, the bracket is
\[
  \langle M^\varepsilon\rangle_t=
      \frac1\varepsilon\int_0^t
       \Gamma_{Q_{X^\varepsilon_s}}(h)(X^\varepsilon_s,Y^\varepsilon_s)\,ds.
\]
If the carré du champ is uniformly bounded by C, then
\[
  \mathbb E\sup_{s\leq T}|\varepsilon M^\varepsilon_s|^2
       \leq4C\varepsilon T.
\]
The bound is coordinatewise for vector h, with a dimension-dependent norm constant. It identifies the exact rate of the averaging error and supplies a reusable estimate for later fluctuation arguments.

Now compare \(X^\varepsilon\) with \(\bar X\). The difference of their integral equations is the sum of this centered environmental integral and
\[
  \int_0^t\bigl(\bar b(X^\varepsilon_s)-\bar b(\bar X_s)\bigr)\,ds.
\]
Lipschitz continuity of \(\bar b\) and Grönwall’s inequality show that \(X^\varepsilon\to\bar X\) uniformly in probability on fixed time intervals.

## 4. The environmental fluctuation scale

The corrector also identifies the leading error. Define
\[
  U^\varepsilon_t=\frac{X^\varepsilon_t-\bar X_t}{\sqrt\varepsilon}.
\]
The corrector identity says that the centered drift, divided by \(\sqrt\varepsilon\), is a martingale term \(\sqrt\varepsilon M^\varepsilon\) plus terms that vanish in probability. Its bracket is order one. For coordinates r and s, define the cross carré du champ
\[
  \Gamma_{Q_x}(h_r,h_s)(y)=\sum_{z\ne y}q_x(y,z)
       (h_r(x,z)-h_r(x,y))(h_s(x,z)-h_s(x,y)).
\]
The averaged covariance rate is
\[
  C_{rs}(x)=\sum_{y\in E}\pi_x(y)
       \Gamma_{Q_x}(h_r,h_s)(y).
\]
Fast mixing replaces the bracket integrand by this invariant average. Linearizing \(\bar b\) around \(\bar X_t\), the candidate limit solves
\[
  dU_t=D\bar b(\bar X_t)U_t\,dt+C(\bar X_t)^{1/2}dB_t.
\]
The square root is any positive semidefinite matrix factor; equivalently, specify a continuous Gaussian martingale with covariance rate C. The limit is a diffusion even though each \(X^\varepsilon\) has continuous finite-variation paths: rapid random switching survives after central-limit rescaling.

This covariance describes environmental fluctuations only. If the slow variable also has its own order-one jump noise, its martingale bracket contributes another covariance term. If population noise is scaled as in Chapter 76, its size relative to \(\sqrt\varepsilon\) depends on the joint limit of N and ε. One must state that relation before adding the two noise sources.

For the martingale limit, the bracket of \(\sqrt\varepsilon M^\varepsilon\) is the time integral of the fast carré du champ without the factor \(1/\varepsilon\). Averaging that bounded integrand along the slow path gives \(\int_0^tC(\bar X_s)ds\). Jumps of the scaled corrector martingale are order \(\sqrt\varepsilon\), so they vanish. The remaining corrector terms also vanish after scaling, leaving the linearized averaged drift and this Gaussian martingale. These are the same bracket and jump checks used in Chapter 75, now with a family of fast generators.

## 5. Green–Kubo form of the covariance

For a frozen x and scalar centered observable \(\widetilde b(x,\cdot)\), the same covariance can be written as
\[
  C(x)=2\int_0^\infty
       \operatorname{Cov}_{\pi_x}\bigl(b(x,Y_0),b(x,Y_s)\bigr)\,ds.
\]
The fast chain in this formula runs with generator \(Q_x\), without the factor \(1/\varepsilon\); that factor has already been absorbed into the fluctuation scaling. The formula follows from the Poisson representation of h and is the Green–Kubo identity from Chapter 74 applied to the frozen environment.

The corrector formula is local in the state and often easier to formalize. It expresses C as a finite rate-weighted sum of squared jump increments. The covariance integral is more intuitive because it shows that persistent correlations increase the effective noise. Both views agree, but the integral representation requires an explicit mixing estimate to justify convergence.

For vector drift, C is positive semidefinite. For any vector \(a\), \(a^TC(x)a\) is the scalar carré du champ average for the corrector \(a\cdot h\), hence is nonnegative. This proof avoids checking eigenvalues of a matrix whose entries are themselves complicated rate sums.

If C has a null direction, the corresponding linear combination of environmental drift has zero long-run variance. For an irreducible finite frozen chain, a scalar zero carré-du-champ average forces its corrector to be constant along every positive-rate edge; centering then makes the corrector zero, and the Poisson equation makes that centered drift identically zero. Thus degeneracy has a structural meaning, not just a matrix-arithmetic explanation.

## 6. Worked example: a two-state switching velocity

Let the fast environment switch from 0 to 1 at rate \(\alpha/\varepsilon\) and from 1 to 0 at rate \(\beta/\varepsilon\), with \(\alpha,\beta>0\). Let the slow coordinate move at velocity c₀ in state 0 and c₁ in state 1. The frozen stationary probabilities are
\[
  \pi(0)=\frac{\beta}{\alpha+\beta},\qquad
  \pi(1)=\frac{\alpha}{\alpha+\beta}.
\]
The averaged velocity and deterministic path are
\[
  \bar c=\frac{\beta c_0+\alpha c_1}{\alpha+\beta},
  \qquad \bar X_t=x_0+\bar c t.
\]
The Poisson equation gives an environmental covariance rate
\[
  C=\frac{2\alpha\beta(c_1-c_0)^2}{(\alpha+\beta)^3}.
\]
Thus \((X^\varepsilon_t-\bar X_t)/\sqrt\varepsilon\) converges to \(\sqrt C B_t\). If c₀=c₁, the environment has no effect on the slow coordinate and C=0. If the switching rates are both multiplied by a common factor, C decreases inversely with that factor: faster decorrelation reduces accumulated error.

This explicit example is a useful sign and scaling check. The raw environmental chain has gap \((\alpha+\beta)/\varepsilon\), so its correlation time is \(\varepsilon/(\alpha+\beta)\). Integrating its centered velocity covariance over a fixed horizon therefore produces variance order \(\varepsilon\), exactly the scale removed by dividing by \(\sqrt\varepsilon\).

## 7. Worked example: an epidemic under fast policy switching

Suppose the SIR state \(x=(s,i,r)\) follows the deterministic vector field
\[
  b(x,y)=\bigl(-\beta_y si,\;\beta_y si-\gamma i,\;\gamma i\bigr),
\]
where \(y\in\{0,1\}\) is a rapidly switching intervention regime. The transition rates of the environment are \(0\to1\) at \(\alpha\) and \(1\to0\) at \(\beta\) on its own fast time scale. Averaging replaces \(\beta_y\) in the ODE by
\[
  \bar\beta=\frac{\beta\,\beta_0+\alpha\,\beta_1}{\alpha+\beta}.
\]
The averaged SIR curve is therefore deterministic. Its leading environmental fluctuation is rank one, because only the infection-rate contrast fluctuates. With \(v(x)=(-si,si,0)\), its covariance rate is
\[
  C(x)=\frac{2\alpha\beta(\beta_1-\beta_0)^2}{(\alpha+\beta)^3}
         v(x)v(x)^T.
\]
The recovery term is common to both regimes and contributes no environmental covariance. This example separates uncertainty caused by policy switching from demographic randomness in infection and recovery events; those are different sources and generally have different scales.

## 8. Dependence on the slow state and initial layers

When \(Q_x\) varies with x, the averaged drift \(\bar b(x)\) inherits dependence from both b and \(\pi_x\). Even if b is smooth, differentiating \(\bar b\) requires control of the derivative of the invariant law. One route differentiates the finite-dimensional equations
\[
  \pi_xQ_x=0,\qquad \sum_y\pi_x(y)=1,
\]
and solves a normalized linear system. Another route differentiates the Poisson corrector equation. Either way, a uniform spectral gap prevents the inverse on the centered subspace from becoming singular.

The initial fast state need not be distributed as \(\pi_{x_0}\) for the law of large numbers. The initial relaxation lasts order \(\varepsilon\) and contributes a vanishing amount to the slow integral. At the fluctuation scale, that initial layer is still typically order \(\sqrt\varepsilon\) after normalization and disappears under bounded correctors. If the initial distribution or transition rates themselves depend on \(\varepsilon\) in a singular way, the initial layer can require a separate analysis.

## 9. Formalization architecture

The reusable interfaces are:

1. a finite fast state type and a generator family \(Q_x\);
2. invariant distributions \(\pi_x\) with normalization and generator identities;
3. a centered-subspace inverse yielding the corrector \(h_x\);
4. uniform bounds and regularity for \(h_x\) as x varies;
5. a joint-process martingale identity and bracket formula;
6. an ODE stability theorem using the corrector estimate;
7. a martingale functional limit theorem for the scaled error.

The proof flow is:

```text
frozen generator Q_x ──> invariant law π_x ──> averaged drift b̄(x)
         │                         │                       │
         └── centered Poisson corrector h_x ──> martingale bracket
                                                        │
                                                        v
                              ODE averaging + Gaussian fluctuation
```

Avoid hiding the x-dependence in an unindexed theorem. The Poisson equation, invariant law, and carré du champ all vary with the slow state. A record can package these fields together, but theorem statements should make the parameter dependence apparent so continuity and uniformity obligations are not lost.

The matrix argument is finite for each fixed x, but proving bounds uniformly over K is a separate analytic step. One useful strategy is to show that the smallest nonzero singular value of \(Q_x\) on the centered subspace is bounded away from zero. Then linear-system estimates control h. This is more robust than repeatedly expanding cofactors in x-dependent rate parameters.

## 10. Common failure modes

### The fast generator is averaged at the wrong state

Use \(\pi_x\), the invariant law of the generator frozen at the current slow state. A single fixed stationary distribution is generally incorrect when \(Q_x\) changes with x.

### Centering is omitted

The Poisson equation is solvable only for a right-hand side with zero \(\pi_x\)-mean. Define \(\bar b(x)\) first and verify centering coordinatewise.

### Uniform mixing is assumed from pointwise irreducibility

Every frozen chain may be irreducible while its spectral gap tends to zero along K. The corrector can then become unbounded. State a uniform gap or prove the bounds directly.

### The corrector drift term is dropped

Applying the joint generator to \(h(X,Y)\) creates the term \(b\cdot\nabla_xh\). It is multiplied by \(\varepsilon\) in the averaging identity, but it must be included before taking limits.

### Environmental and demographic noises are merged

The fast-environment covariance comes from the corrector bracket. Population jump noise comes from the slow generator. Combine them only after specifying their joint scaling.

### A finite-time theorem is used for stationary laws

Uniform-in-time stability and tightness are additional requirements. Averaging on each fixed interval does not imply convergence of invariant distributions.

## 11. Exercises

1. Prove that \(\widetilde b(x,\cdot)\) has zero mean under \(\pi_x\).
2. Derive the corrector identity by applying the joint generator martingale theorem.
3. Bound the bracket of \(\varepsilon M^\varepsilon\) on a fixed interval.
4. Use Grönwall’s inequality to obtain uniform convergence to the averaged ODE.
5. Compute the covariance rate for a two-state switching velocity.
6. Derive the Green–Kubo expression from the frozen Poisson equation.
7. Formulate the covariance matrix for a vector-valued slow drift and prove positive semidefiniteness.
8. Average the SIR drift under two policy regimes and compute its environmental covariance.
9. Give an example where each \(Q_x\) is irreducible but no uniform spectral gap exists over K.
10. Explain why a stationary-limit theorem requires more than finite-horizon averaging.

## Summary

A rapidly switching finite-state environment drives a slow variable through a drift \(b(x,y)\). Averaging uses the invariant law \(\pi_x\) of the frozen fast generator to form \(\bar b(x)\). A parameter-dependent Poisson corrector turns the centered drift integral into a small endpoint and drift correction plus a martingale. Its bracket gives the leading environmental covariance and a Gaussian fluctuation diffusion. Uniform mixing, corrector regularity, path localization, and the scale of any additional jump noise must be stated explicitly.

## Further reading

- Chapters 74–76 for Poisson equations, functional central limit theorems, and population diffusion limits.
- G. Yin and H. Zhang, “Two-Time-Scale Markov Chains and Applications to Quasi-Birth-Death Queues,” *SIAM Journal on Applied Mathematics* 65 (2005), 1005–1026, [doi:10.1137/S003613990139756X](https://doi.org/10.1137/S003613990139756X).
