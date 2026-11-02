# Chapter 76 — Population Scaling and Diffusion Limits

> **Audience.** This chapter assumes continuous-time jump processes, generator martingales, ordinary differential equations, and the functional central limit theorem. It studies large population models through deterministic fluid limits and Gaussian fluctuation processes.

Many stochastic population models have a natural size parameter N. The state records integer population counts, transition rates grow proportionally to N, and individual jumps change the normalized population by order \(1/N\). As N grows, the density path approaches a deterministic solution of an ordinary differential equation. Its deviations from that trajectory, multiplied by \(\sqrt N\), converge on fixed time intervals to a Gaussian diffusion.

This scaling limit turns a large jump process into two successive approximations: first an ODE for the macroscopic state, then a linear stochastic differential equation for fluctuations. The formalization reuses generator and martingale ideas from earlier chapters, but must manage a sequence of state spaces, differentiability of the drift, and matrix-valued quadratic variation.

## Learning objectives

By the end of the chapter, you should be able to:

- define a density-dependent family of jump processes;
- derive its drift and covariance functions from the jump channels;
- prove a fluid limit by martingale estimates and Grönwall’s inequality;
- linearize the drift to obtain the Gaussian fluctuation equation;
- compute the fluctuation covariance through a matrix differential equation;
- distinguish a finite-time diffusion limit from a stationary approximation.

## 1. Jump channels and density scaling

Fix a finite set of jump vectors \(\mathcal J\subset\mathbb Z^d\). For each size parameter \(N\), let \(X_N(t)\) be an integer-valued population process. A channel with vector v changes the count by v, at rate
\[
  N\beta_v(Z_N(t)),\qquad Z_N(t)=\frac{X_N(t)}{N},
\]
where \(\beta_v\) is a nonnegative rate function of the current density. Thus the density jump is \(v/N\), while the event rate is order N. Assume for now that the density stays in a compact invariant set K, the functions \(\beta_v\) are bounded and continuously differentiable there, and the number of channels is finite.

A channel that would leave the allowed state space must have zero rate at that state. This boundary convention is part of the model, not an automatic consequence of the formula for \(\beta_v\). It ensures the generator only sums over valid transitions and is especially important for population counts near extinction or capacity limits.

The generator acting on a test function \(\varphi\) is
\[
  L_N\varphi(x)=N\sum_{v\in\mathcal J}\beta_v(x)
          \left[\varphi\left(x+\frac vN\right)-\varphi(x)\right].
\]
Two functions summarize the model:
\[
  F(x)=\sum_{v\in\mathcal J}v\beta_v(x),\qquad
  A(x)=\sum_{v\in\mathcal J}vv^{T}\beta_v(x).
\]
The vector F is the macroscopic drift. The positive semidefinite matrix A is the instantaneous covariance accumulated from jumps.

This channel representation is preferable to listing every entry of a large generator matrix. It separates stoichiometry, encoded by v, from state-dependent intensity, encoded by \(\beta_v\). It also makes scaling transparent: first-order increments produce F, while squared increments produce covariance of order \(1/N\).

The finite-channel assumption is convenient rather than essential. With infinitely many possible jump vectors, the drift and covariance sums must converge, and a tail condition must prevent rare large jumps from contributing at the central-limit scale. A Lean development can first establish the finite-channel theorem, then generalize by truncation once uniform tail estimates are available.

## 2. Generator expansion and martingale representation

For a smooth scalar test function, Taylor expansion gives
\[
  L_N\varphi(x)=\nabla\varphi(x)\cdot F(x)+O(N^{-1}),
\]
uniformly on compact subsets where second derivatives are bounded. The first-order term is the generator of the deterministic flow \(\dot x=F(x)\). The second-order Taylor term records the leading stochastic correction and involves A.

Applying the generator martingale theorem to coordinate functions yields
\[
  Z_N(t)=Z_N(0)+\int_0^tF(Z_N(s))\,ds+M_N(t),
\]
where \(M_N\) is a vector martingale. Its predictable covariance matrix is
\[
  \langle M_N\rangle_t=\frac1N\int_0^tA(Z_N(s))\,ds.
\]
More precisely, the (r,s) entry of the bracket is the predictable covariation of coordinate martingales r and s. This formula follows by summing the rate of each channel times the outer product of its density increment \(v/N\).

The scaling can be checked dimensionally. There are order N events per unit time, each density jump has size order \(1/N\), so mean drift is order one and variance rate is order \(N\cdot N^{-2}=N^{-1}\). Therefore the density noise vanishes in the law-of-large-numbers limit, but multiplying its martingale part by \(\sqrt N\) leaves order-one fluctuations.

## 3. The fluid limit

Let \(x(t)\) solve the deterministic initial-value problem
\[
  \dot x(t)=F(x(t)),\qquad x(0)=x_0.
\]
If F is Lipschitz on K and \(Z_N(0)\to x_0\) in probability, then for each finite horizon T,
\[
  \sup_{0\leq t\leq T}|Z_N(t)-x(t)|\longrightarrow0
  \quad\text{in probability}.
\]
The proof is a perturbation argument. Subtract the integral equation for x from the martingale equation for \(Z_N\):
\[
  |Z_N(t)-x(t)|\leq|Z_N(0)-x_0|+\sup_{s\leq T}|M_N(s)|
       +L\int_0^t|Z_N(s)-x(s)|\,ds.
\]
Doob’s inequality and the bracket bound show \(\sup_{s\leq T}|M_N(s)|\to0\) in probability. Grönwall’s inequality then controls the pathwise error uniformly over the horizon.

The estimate can be made explicit under the boundedness assumptions. If \(\operatorname{tr}A(x)\leq C\) on K, then
\[
  \mathbb E\left[\sup_{s\leq T}|M_N(s)|^2\right]
       \leq \frac{4CT}{N}.
\]
Consequently the density error is bounded by \(e^{LT}(|Z_N(0)-x_0|+\sup_{s\leq T}|M_N(s)|)\). The exponential factor depends on the fixed horizon; this is one reason the result is stated on compact time intervals. The bound also makes a clean Lean lemma: derive a bracket trace estimate, apply a vector martingale maximal inequality, then use a deterministic Grönwall theorem.

The compactness and bounded-rate assumptions do real work. If the state can escape to infinity, one first proves compact containment or stops the process on leaving a large set. If rates grow too quickly, explosion or large excursions can defeat the martingale estimate. A local Taylor expansion alone is not a fluid-limit proof; one also has to show that the process remains where the expansion is valid.

## 4. The fluctuation process

Assume the initial density is accurate at the central-limit scale: \(\sqrt N(Z_N(0)-x_0)\to u_0\). Define
\[
  U_N(t)=\sqrt N\,(Z_N(t)-x(t)).
\]
The density martingale becomes \(W_N=\sqrt N M_N\), whose bracket is
\[
  \langle W_N\rangle_t=\int_0^tA(Z_N(s))\,ds.
\]
The fluid limit and continuity of A suggest convergence of this bracket to \(\int_0^tA(x(s))ds\). Each scaled jump of \(W_N\) has size \(v/\sqrt N\), which vanishes because the jump set is finite.

Linearize F around the deterministic path. Writing \(J(t)=DF(x(t))\), the candidate fluctuation limit U solves
\[
  dU(t)=J(t)U(t)\,dt+dG(t),\qquad U(0)=u_0,
\]
where G is a continuous Gaussian martingale with covariance rate A(x(t)). Equivalently, when a matrix square root is selected,
\[
  dU(t)=J(t)U(t)\,dt+A(x(t))^{1/2}\,dB(t).
\]
This is a time-inhomogeneous linear diffusion, often called the linear noise approximation.

The fluctuation theorem asserts weak convergence of \(U_N\) in a path space over each finite interval. Its proof combines the martingale functional central limit theorem with a Taylor remainder estimate. The drift difference satisfies
\[
  \sqrt N\bigl(F(Z_N)-F(x)\bigr)=J(t)U_N+\text{remainder},
\]
and a locally Lipschitz derivative makes the integrated remainder vanish in probability after localization. Unlike the fluid limit, the fluctuation theorem needs the rate of initial convergence and second-order control of the drift.

For example, if DF is locally Lipschitz with constant C on the region under consideration, then
\[
  |F(z)-F(x)-DF(x)(z-x)|\leq C|z-x|^2.
\]
After multiplying by \(\sqrt N\), the remainder is bounded by \(C|U_N|^2/\sqrt N\). Tightness of \(U_N\) on a fixed interval, followed by localization to a large ball, makes its time integral vanish in probability. This is why the fluctuation proof first controls the scaled martingale and the linear drift, then treats the Taylor remainder; a pointwise Taylor formula alone does not give convergence of the integrated error.

## 5. Covariance dynamics

For deterministic \(u_0\), U is Gaussian with mean transported by the linear drift. Its covariance matrix \(V(t)=\operatorname{Cov}(U(t))\) satisfies the matrix differential equation
\[
  \dot V(t)=J(t)V(t)+V(t)J(t)^T+A(x(t)),\qquad V(0)=0.
\]
The first two terms transport existing covariance under the linearized drift; the final term adds covariance from new jumps. The mean is \(m(t)=\Phi(t,0)u_0\). For a random initial fluctuation with covariance \(V_0\), replace the initial condition by \(V(0)=V_0\), assuming the initial limit is appropriately independent of future noise. The formula for \(V\) concerns covariance, not the uncentered second moment when the mean is nonzero.

The covariance equation is often more useful than explicitly solving the SDE. It is finite-dimensional, deterministic, and supports sensitivity analysis. It also makes the role of unstable equilibria visible: if J has a positive direction, existing perturbations can grow rather than settle into a stationary Gaussian law.

Let \(\Phi(t,s)\) be the fundamental matrix solving \(\partial_t\Phi(t,s)=J(t)\Phi(t,s)\) and \(\Phi(s,s)=I\). Then the covariance has the variation-of-constants representation
\[
  V(t)=\Phi(t,0)V_0\Phi(t,0)^T
       +\int_0^t\Phi(t,s)A(x(s))\Phi(t,s)^T\,ds.
\]
This formula separates transported initial uncertainty from noise accumulated after time zero. Differentiating it recovers the matrix Lyapunov equation, while direct evaluation can be convenient in a model with an explicitly solvable deterministic trajectory.

For a time-homogeneous equilibrium \(x_*\) with \(F(x_*)=0\), set \(J=DF(x_*)\) and \(A_*=A(x_*)\). If every eigenvalue of J has negative real part, the stationary covariance candidate solves the Lyapunov equation
\[
  JV+VJ^T+A_*=0.
\]
This equilibrium calculation is distinct from a finite-horizon diffusion limit. To prove convergence of stationary distributions of the original population chains, one also needs uniform tightness and control of long-time behavior as N grows.

## 6. Worked example: linear birth and death

Consider a population with births at rate \(N\lambda x\) and deaths at rate \(N\mu x\), where x is its density and \(\lambda,\mu>0\). The two jump vectors are +1 and −1. Thus
\[
  F(x)=(\lambda-\mu)x,\qquad A(x)=(\lambda+\mu)x.
\]
The deterministic trajectory is \(x(t)=x_0e^{rt}\), where \(r=\lambda-\mu\). The scalar fluctuation equation is
\[
  dU(t)=rU(t)\,dt+\sqrt{(\lambda+\mu)x_0e^{rt}}\,dB(t).
\]
For deterministic initial density accurate at scale \(1/\sqrt N\), the initial fluctuation is zero. Its variance solves
\[
  V'(t)=2rV(t)+(\lambda+\mu)x_0e^{rt},\qquad V(0)=0.
\]
For r≠0, integration gives
\[
  V(t)=(\lambda+\mu)x_0e^{2rt}\frac{1-e^{-rt}}r.
\]
The unbounded birth model does not have a globally invariant compact density set, so this calculation uses the localized finite-horizon version of the theorem: stop outside a compact neighborhood of the ODE path, prove the stopped limit, then show the exit probability vanishes as the neighborhood expands. Linear birth and death processes are non-explosive on finite intervals, and the ODE trajectory is bounded on each such interval. This localization separates a harmless unbounded state space from a genuine failure of compact-time control.

At the critical case \(\lambda=\mu\), the continuous limit of this expression is \(V(t)=2\lambda x_0t\). The explicit solution checks both the drift linearization and the covariance scaling. When r>0 fluctuations grow with the population; when r<0 the deterministic population decays, and finite-time Gaussian approximations eventually become poor near extinction.

## 7. Worked example: an SIR epidemic

Let \(x=(s,i,r)\) denote susceptible, infectious, and removed fractions. Infection changes one susceptible into one infectious individual, with vector \(v_1=(-1,1,0)\) and rate \(N\beta si\). Recovery has vector \(v_2=(0,-1,1)\) and rate \(N\gamma i\). The drift is
\[
  F(s,i,r)=(-\beta si,\;\beta si-\gamma i,\;\gamma i),
\]
and the covariance rate is
\[
  A(s,i,r)=\beta si\,v_1v_1^T+\gamma i\,v_2v_2^T.
\]
The ODE describes the deterministic epidemic curve. Along that curve, the Gaussian fluctuation covariance solves the time-varying Lyapunov equation with \(J(t)=DF(x(t))\) and the displayed A. The total population fraction remains one because every jump vector has coordinate sum zero; the covariance is correspondingly degenerate in the all-ones direction.

This example shows why reaction channels should be kept explicit. The two event types contribute separate rank-one matrices to A, and conservation is visible as a linear invariant. In Lean, one can prove the conservation identity channel by channel before expanding the matrix covariance. The density process lives in a simplex, so boundary behavior still requires attention if the deterministic path approaches a face where some rates vanish.

## 8. Boundary effects and validity of the approximation

The Gaussian fluctuation process takes values in all of \(\mathbb R^d\), even when the population density is constrained to a simplex or orthant. This is harmless on a fixed time interval when the deterministic trajectory stays a positive distance from the boundary and fluctuations are of order \(N^{-1/2}\). Near extinction or a reflecting boundary, the Gaussian model may assign substantial probability to impossible negative counts.

At such boundaries, the correct limit may require reflection, absorption, a branching-process approximation, or a different scaling. The interior diffusion approximation should not be extended through a boundary merely because its coefficients have a formal limit there. Identify the state-space constraints and prove the deterministic path remains in a regular region, or state a boundary-specific theorem.

There is also a time-horizon restriction. Standard fluid and fluctuation limits hold on each fixed compact time interval. If the deterministic dynamics approach equilibrium only over times that grow with N, the error estimates may not remain uniform. A stationary Gaussian approximation needs separate stability and tightness arguments, not only the finite-time central limit theorem.

## 9. Formalization architecture

Represent the family with a fixed finite set of channels and a rate function for each channel. Keep the state space, density embedding, and jump scaling explicit. Then develop the theorem in layers:

1. finite sums define the drift F and covariance A;
2. coordinate generator identities produce the martingale and bracket;
3. a martingale estimate and Grönwall prove the fluid limit;
4. differentiability gives the linearized drift and a controlled Taylor remainder;
5. a martingale functional limit theorem identifies the Gaussian noise;
6. a continuous-mapping or SDE uniqueness result identifies the fluctuation limit.

The dependency structure is:

```text
channel rates + jump vectors ──> drift F and covariance A
             │                             │
             v                             v
   generator martingale ──> fluid ODE ──> Jacobian along the path
             │                             │
             └──── scaled bracket ─────────┘
                            │
                            v
                linear Gaussian fluctuation
```

For a formal proof, specify a common probability space only if the theorem is strong or almost-sure. A weak-convergence result needs laws on path spaces and tightness; it does not require a coupling that makes every N-process converge pointwise. This distinction avoids proving a stronger representation theorem when distributional convergence is the actual goal.

The most reusable algebraic lemma is the generator expansion for a coordinate or quadratic test function. Prove it from the finite channel sum, then derive drift and bracket statements by specializing the test function. For the central limit scale, separate the Taylor remainder estimate from the martingale convergence theorem so regularity assumptions remain visible.

## 10. Common failure modes

### The jump-size and rate scalings are mixed

Density jumps are \(v/N\), not v, while event rates are \(N\beta_v\). Their product gives order-one drift; their squared product gives order-\(1/N\) bracket.

### The ODE limit is stated without containment

Local Lipschitz regularity does not prevent the chain from leaving the region where rates are controlled. Prove compact containment or stop and localize.

### The covariance omits a reaction channel

Every channel contributes \(\beta_v vv^T\). Preserve the channel sum until all drift and covariance identities are derived.

### The fluctuation drift uses F instead of DF

The central-limit process describes deviations around x(t); its linear drift is the Jacobian \(DF(x(t))\), not the original nonlinear vector field.

### A finite-time approximation is treated as stationary

Long-time convergence of invariant distributions requires uniform-in-N arguments beyond the fixed-horizon diffusion theorem.

### A Gaussian path is forced through a hard boundary

Near extinction or reflection, the interior linear-noise approximation can leave the feasible region. Use a boundary-aware scaling theorem.

## 11. Exercises

1. Derive F and A for a general finite set of jump channels.
2. Compute the generator applied to a linear coordinate and verify the martingale drift.
3. Prove the fluid-limit estimate from Doob’s inequality and Grönwall’s lemma.
4. Derive the scaled bracket of \(\sqrt N M_N\).
5. Linearize F and identify the fluctuation SDE.
6. Solve the covariance equation for the linear birth-death example.
7. Derive the SIR drift and covariance from its two reaction vectors.
8. Prove that the SIR covariance is degenerate in the conserved all-ones direction.
9. Give an example where a finite-time diffusion limit does not imply a stationary Gaussian approximation.
10. State a localization condition that makes the Taylor remainder uniform.

## Summary

Density-dependent jump processes have order-\(1/N\) density jumps at order-N rates. Their drift converges to an ODE, while \(\sqrt N\)-scaled deviations converge on fixed time intervals to a linear Gaussian diffusion. The drift and covariance are finite sums over reaction channels; the main proof ingredients are martingale estimates, Grönwall, a Taylor expansion, and a martingale functional central limit theorem. Boundary behavior and stationary limits require additional hypotheses.

## Further reading

- Chapters 55, 58, and 75 for continuous-time generators, martingales, and functional limit theorems.
- T. G. Kurtz, “Solutions of Ordinary Differential Equations as Limits of Pure Jump Markov Processes,” *Journal of Applied Probability* 7 (1970), 49–58, [doi:10.2307/3212147](https://doi.org/10.2307/3212147).
- T. G. Kurtz, “Limit Theorems for Sequences of Jump Markov Processes Approximating Ordinary Differential Processes,” *Journal of Applied Probability* 8 (1971), 344–356, [doi:10.2307/3211904](https://doi.org/10.2307/3211904).
