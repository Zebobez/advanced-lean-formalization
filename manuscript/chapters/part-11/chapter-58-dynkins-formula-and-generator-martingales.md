# Chapter 58 — Dynkin’s Formula and Generator Martingales

> **Audience.** This chapter assumes familiarity with finite-state continuous-time Markov chains, conditional expectation, filtrations, and martingales. It derives the basic expectation identity for a generator and the martingale that records its centered drift.

The generator is more than a compact encoding of transition rates. Applied to an observable, it gives the instantaneous expected rate of change of that observable. Integrating this rate yields Dynkin’s formula. Subtracting the accumulated drift from the observed change produces a martingale.

For finite-state chains, the argument has two layers. Matrix calculus proves an operator identity for the transition semigroup. The Markov property then upgrades the expectation identity to a conditional one, which is exactly the martingale property. Keeping these layers separate turns an advanced stochastic theorem into a sequence of finite-dimensional algebra, integration, and conditional-expectation lemmas.

## Learning objectives

By the end of the chapter, you should be able to:

- apply a generator to a real-valued observable;
- derive Dynkin’s formula from the semigroup differential equation;
- define the compensated observable martingale;
- prove its conditional-increment identity from the Markov property;
- use bounded stopping times to obtain stopped expectation formulas;
- organize the Lean proof around operator, process, and filtration interfaces.

## 1. The generator acting on observables

Let S be a finite state space and Q a generator. A real-valued observable is a function f:S→ℝ. The generator acts by
\[
  (Qf)(x)=\sum_y q_{xy}f(y)
        =\sum_{y\ne x}q_{xy}\bigl(f(y)-f(x)\bigr).
\]
The second equality uses the zero row-sum equation. It expresses the instantaneous drift as the sum, over possible destinations, of rate times change in the observable.

This formula explains the sign of Qf. A state can have positive drift for one observable and negative drift for another. The generator itself is not a probability transition operator: its rows sum to zero, and its diagonal is usually negative. The transition operator at time t is P_t=e^{tQ}, which does preserve constants and nonnegative functions.

View f as a column vector. Then P_t f is the function
\[
  (P_t f)(x)=\sum_yP_t(x,y)f(y).
\]
It gives the conditional expectation of the future observable when the chain starts at x. The backward equation gives
\[
  \frac{d}{dt}P_t f=QP_t f=P_tQf.
\]
The equality of the two expressions uses commutation of Q with its exponential. The form P_tQf will be useful because it can be integrated directly.

On a finite state space every real-valued observable is bounded. Thus f(X_t), Qf(X_t), and the finite-time integrals below are integrable under any probability law. This simple finiteness fact removes several technical hypotheses that matter on general state spaces.

## 2. The semigroup integral identity

Integrate the derivative of P_t f from zero to t. Since P₀ is the identity,
\[
  P_t f-f=\int_0^t P_sQf\,ds.
\]
This is an identity of functions on S. Because S is finite, it can be proved entry by entry or as a vector-valued integral. No stochastic process is needed for this step; only the matrix semigroup and ordinary calculus are involved.

The identity is often the most efficient formal target. It packages all starting states and all terminal observables into one equation. A proof that begins with random variables may instead become entangled in sample-space notation before the finite-dimensional calculus has been established.

For a chain with initial law μ, average the identity over X₀:
\[
  \mathbb E_\mu[f(X_t)]-\mathbb E_\mu[f(X_0)]
   =\int_0^t\mathbb E_\mu[(Qf)(X_s)]\,ds.
\]
To justify the right-hand side, use the Markov transition law at each time s and interchange expectation and a finite-time integral. In a finite-state model the integrand is bounded by the largest absolute value of Qf, so the integrability condition is immediate.

This expectation equation is Dynkin’s formula in its deterministic-time form. It says that the change in expected observable equals the expected accumulated generator drift. It applies to any f, not only to eigenfunctions, harmonic functions, or indicators.

## 3. The compensated process

For a process X with generator Q, define
\[
  M_t=f(X_t)-f(X_0)-\int_0^t(Qf)(X_s)\,ds.
\]
The first two terms record the observed change. The integral subtracts the drift predicted by the generator. The result is a martingale with respect to a filtration for which X has the Markov property and is adapted.

The process M is integrable on every bounded time interval. If \(\|f\|_\infty\) and \(\|Qf\|_\infty\) denote maximum absolute values on S, then
\[
  |M_t|\leq 2\|f\|_\infty+t\|Qf\|_\infty.
\]
The bound is deterministic and finite for each t. It will also help with optional sampling on a bounded time horizon.

The martingale property is stronger than \(\mathbb E[M_t]=\mathbb E[M_0]\). It requires that for every s≤t,
\[
  \mathbb E[M_t\mid\mathcal F_s]=M_s
\]
almost surely. This conditional statement is where the Markov property enters. The semigroup integral identity alone proves only the unconditional expectation equation.

## 4. Conditional-increment proof

Fix 0≤s≤t. The Markov property gives
\[
  \mathbb E[f(X_t)\mid\mathcal F_s]
    =(P_{t-s}f)(X_s).
\]
For the drift integral, conditional Fubini and the same Markov property yield
\[
  \mathbb E\!\left[
    \int_s^t(Qf)(X_u)\,du\ \middle|\ \mathcal F_s
  \right]
  =\int_s^t(P_{u-s}Qf)(X_s)\,du.
\]
Apply the semigroup integral identity over the interval of length t−s:
\[
  \int_s^tP_{u-s}Qf\,du=P_{t-s}f-f.
\]
Evaluating at X_s shows that the conditional expectation of the increment in f is exactly the conditional expected drift:
\[
  \mathbb E[f(X_t)-f(X_s)\mid\mathcal F_s]
  =
  \mathbb E\!\left[
    \int_s^t(Qf)(X_u)\,du\ \middle|\ \mathcal F_s
  \right].
\]
Subtract the right-hand side to obtain
\[
  \mathbb E[M_t-M_s\mid\mathcal F_s]=0.
\]
This proves the martingale identity.

Every equality above has a distinct formal role. The first is the Markov property as a conditional law statement. The second moves conditional expectation through a time integral. The third is deterministic semigroup calculus. The final step uses linearity of conditional expectation. Naming these intermediate results makes a Lean proof easier to diagnose than a single large conditional-expectation calculation.

In a finite state space, conditional expectations of functions of X_u can often be reduced to finite sums over states. That calculation is especially useful when there is no general theorem available for the specific process-level integral. Once the finite-state identity is isolated, the remaining analytic task is to justify the time integral and its conditional interchange.

## 5. Worked example: the indicator of one state

Return to a two-state chain with rate a from 0 to 1 and rate b from 1 to 0. Let f be the indicator of state 1:
\[
  f(0)=0,\qquad f(1)=1.
\]
Then
\[
  (Qf)(0)=a,\qquad (Qf)(1)=-b.
\]
The compensated martingale is
\[
  M_t=\mathbf 1_{\{X_t=1\}}-\mathbf 1_{\{X_0=1\}}
      -\int_0^t\bigl(a\mathbf 1_{\{X_s=0\}}
                     -b\mathbf 1_{\{X_s=1\}}\bigr)\,ds.
\]
When the chain is in state 0, the indicator tends to increase at rate a. When it is in state 1, it tends to decrease at rate b. The integral subtracts exactly those conditional rates.

Taking expectations gives the balance equation
\[
  \Pr(X_t=1)-\Pr(X_0=1)
   =\int_0^t\left(a\Pr(X_s=0)-b\Pr(X_s=1)\right)ds.
\]
This is the forward equation for the probability of state 1. Thus the scalar Kolmogorov equation is a special case of Dynkin’s formula applied to an indicator.

This example is ideal for formalization. The function f has only two values, Qf can be computed by cases, and the indicator of each state is measurable for the discrete sigma-algebra. The process-level proof still needs the Markov conditional law, but the algebraic part can be normalized by a short finite case split.

## 6. Worked example: harmonic functions and hitting probabilities

Suppose A⊆S is a target set and f is harmonic outside A:
\[
  (Qf)(x)=0\qquad(x\notin A).
\]
Let τ_A be the first hitting time of A. Before τ_A, the generator drift of f vanishes. The stopped process f(X_{t∧τ_A}) is therefore a martingale under suitable integrability conditions. If f is bounded, then on every finite horizon these conditions follow automatically.

If the chain is absorbed upon reaching A and the stopping time is almost surely finite, take expectations and pass to the limit in the stopped identity. The value f(X_{τ_A}) is then determined by the boundary values of f on A. For example, choosing boundary values 1 on a desired portion of A and 0 on the rest makes f(x) the probability of hitting the first portion before the second, provided the boundary-value problem has a unique solution.

This turns a probabilistic hitting question into a finite linear system for Qf=0 away from the boundary. Conversely, a martingale proof explains why the solution of that linear system has the desired probability interpretation. In Lean, it is often productive to formalize the linear system and its uniqueness first, then connect it to the stopped process using optional sampling.

The limiting step needs care. Optional sampling at τ_A∧T is available for bounded T. To let T grow, one must show τ_A is finite almost surely and justify convergence of the stopped values, often by bounded convergence. Do not replace this argument with an unqualified application of optional stopping at an unbounded time.

### Example: expected absorption time

Consider the one-way chain with states 0 and 1, rate d>0 from 1 to 0,
and 0 absorbing. Let h(0)=0 and h(1)=1/d. Then
\[
  (Qh)(1)=d\bigl(h(0)-h(1)\bigr)=-1,
  \qquad
  (Qh)(0)=0.
\]
Let τ₀ be the first time the chain reaches 0. Apply stopped Dynkin at
τ₀∧T, starting from 1. Before τ₀ the state is 1, so the integrated drift is
−(τ₀∧T). Therefore
\[
  \mathbb E[h(X_{\tau_0\wedge T})]
    =\frac1d-\mathbb E[\tau_0\wedge T].
\]
The holding time τ₀ is exponential with rate d, hence finite almost surely
and has mean 1/d. As T tends to infinity, the stopped value on the left
tends to h(0)=0 and is bounded by 1/d. Bounded convergence then recovers
\(\mathbb E[\tau_0]=1/d\).

The same calculation is the solution of the finite boundary-value problem
Qh=−1 away from the absorbing state, with h(0)=0. In more complicated
chains, solving this linear system can yield expected hitting times before
the pathwise argument is carried out.

## 7. Dynkin’s formula at a stopping time

For a bounded stopping time τ, optional sampling of M gives
\[
  \mathbb E[f(X_\tau)]
  =\mathbb E[f(X_0)]
   +\mathbb E\!\left[\int_0^\tau(Qf)(X_s)\,ds\right].
\]
One can first apply optional sampling to τ∧T, where T is deterministic, and then use the fact that τ is bounded by T. On a finite state space, f and Qf are bounded, so the stopped martingale is integrable.

The stopped formula is useful for expected occupation times. If f is the indicator of a state x, then
\[
  \int_0^\tau f(X_s)\,ds
\]
is the amount of time spent in x before τ. Choosing a function whose generator is a convenient constant over a region can turn Dynkin’s formula into a bound on expected exit times.

For unbounded stopping times, additional conditions are needed: uniform integrability of the stopped martingale, integrability of the stopping time, or a suitable localization argument. Finite state does not automatically make τ bounded. The state values are bounded, but the time integral can grow with τ.

## 8. A generator view of jump compensation

There is another interpretation of the same martingale. Along a sample path,
\[
  f(X_t)-f(X_0)
  =\sum_{0<s\leq t:\,X_s\ne X_{s-}}
     \bigl(f(X_s)-f(X_{s-})\bigr).
\]
Each genuine jump contributes a discrete increment. Given the current state x, the conditional rate of an increment to y is q_xy, so the expected instantaneous increment is
\[
  \sum_{y\ne x}q_{xy}\bigl(f(y)-f(x)\bigr)=(Qf)(x).
\]
Subtracting the integrated rate centers the jump sum, leaving a martingale.

This compensated-jump description is more detailed than Dynkin’s formula. It can prove results about individual transition counts and jump sizes, but it introduces counting processes and predictable intensities. The semigroup proof is usually simpler when the theorem concerns only f(X_t). A library development should choose the formulation demanded by the result rather than defining compensators as a prerequisite for every expectation identity.

Uniformization gives a discrete event version of this explanation. At each candidate event, the conditional expected change in f is (Rf)(x)−f(x), and
\[
  \Lambda\bigl((Rf)(x)-f(x)\bigr)=(Qf)(x).
\]
The equality follows from R=I+Q/Λ. Thus the generator drift is the candidate event rate multiplied by the mean change per event. Self-transitions contribute zero change and cause no difficulty.

### Time-dependent observables

The same reasoning applies when the observable depends on time. For a
differentiable function g(t,x), the instantaneous drift has two terms:
\[
  \partial_t g(t,x)+(Qg_t)(x),
\]
where g_t is the state function obtained by fixing t. The compensated process
\[
  g(t,X_t)-g(0,X_0)
   -\int_0^t\bigl(\partial_sg(s,X_s)+(Qg_s)(X_s)\bigr)\,ds
\]
is a martingale under the same finite-state boundedness assumptions on
bounded time intervals. The extra derivative accounts for the observable
changing even while the chain remains in one state. This space-time form is
the finite-state version of the backward equation for time-dependent
problems.

For a formal proof, combine the product rule in time with the generator
identity for each fixed state. Keeping the partial derivative and the
state-transition term separate makes sign errors easier to detect and gives
a reusable lemma for time-inhomogeneous boundary-value problems.

## 9. Lean proof architecture

Separate the development into four interfaces:

1. **Finite operator calculus:** define Qf and prove the semigroup integral identity.
2. **Markov conditional law:** express the conditional expectation of f(X_t) given information at time s using P_{t-s}.
3. **Conditional integration:** exchange conditional expectation and the time integral under boundedness and measurability assumptions.
4. **Martingale and stopping:** package the compensated process, prove its conditional-increment property, and invoke optional sampling when its hypotheses are met.

The current Mathlib martingale interface is built around a filtration, a strongly adapted process, and conditional-expectation identities, with integrability assumptions supplied where required. The adapted-process interface also contains measurability and progressive-measurability notions. Optional-sampling theorems provide stopping-time results for abstract martingales. These are reusable components, but they do not by themselves prove Dynkin’s formula for a chosen continuous-time Markov chain.

A useful finite-state lemma states, for each x and t,
\[
  (P_t f)(x)-f(x)=\int_0^t(P_s(Qf))(x)\,ds.
\]
Keep its assumptions explicit: finite S, generator row sums, the semigroup differential equation, and continuity of the integrand. Then the process argument can invoke this lemma without unfolding matrix exponentials.

When representing time, choose a linearly ordered type compatible with the filtration interface, such as nonnegative reals, and record the coercions between natural-number time, real time, and nonnegative real time. When applying an abstract optional-sampling result, match its boundedness and filtration conditions exactly. A theorem about a discrete index may not apply to a continuous index merely because both are ordered.

For finite S, boundedness proofs should be centralized. Establish maximum bounds for f and Qf once, derive integrability of f(X_t) and the drift integral for every fixed t, and reuse those results in the martingale constructor. This avoids repeated case splits over states and makes the probabilistic assumptions easy to audit.

## 10. Exercises

1. Prove the semigroup integral identity from the backward equation.
2. Derive the expectation form of Dynkin’s formula by averaging over the initial distribution.
3. For the two-state chain, compute Qf when f is the indicator of state 0.
4. Show that the compensated process has conditional mean-zero increments.
5. Identify exactly where the Markov property is used in the martingale proof.
6. Prove the stopped Dynkin formula for a stopping time bounded by a deterministic T.
7. Formulate a finite Dirichlet problem for the probability of hitting one boundary subset before another.
8. Explain why bounded state observables do not imply integrability at an unbounded stopping time for the drift integral.
9. Compare the semigroup proof with the compensated-jump proof.
10. Use uniformization to verify that the expected change per unit time is Qf.

## Summary

For a finite-state chain, the semigroup satisfies P_t f−f=∫₀ᵗP_sQf ds. This is Dynkin’s formula at deterministic times. The Markov property turns it into a conditional-increment identity, showing that f(X_t) minus its initial value and accumulated generator drift is a martingale. Bounded stopping times then yield a stopped expectation formula. In Lean, finite operator calculus, conditional transition laws, conditional integration, and abstract martingale theorems should remain separate interfaces.

## Further reading

- [Mathlib: Martingales](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Basic.html)
- [Mathlib: Adapted and progressively measurable processes](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Adapted.html)
- [Mathlib: Optional sampling](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/OptionalSampling.html)
- [Mathlib: Filtrations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Filtration.html)
- Chapters 32, 35–37, and 55–57 for integration, conditional expectation, filtrations, and continuous-time chains.
