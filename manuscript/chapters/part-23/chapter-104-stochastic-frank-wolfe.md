# Chapter 104 — Stochastic Frank–Wolfe and Noisy Linear Oracles

> **Audience.** This chapter assumes stochastic-gradient estimates from Chapter 95, control variates from Chapter 96, and the nonconvex stationarity gap from Chapter 103. It studies how sampling noise affects the linear-oracle direction and the expected FW-gap guarantee.

In stochastic optimization, the gradient used by Frank–Wolfe is often an estimate. The resulting atom is not an unbiased estimate of the exact oracle atom: minimizing a noisy linear function is a nonlinear operation. This makes stochastic Frank–Wolfe different from simply inserting an unbiased gradient into a deterministic proof.

A useful analysis separates three quantities: the true FW gap of the current point, the noisy gap of the sampled linear problem, and the true directional decrease along the atom selected from the noisy gradient. Their differences can be bounded by the gradient estimation error and the feasible-set diameter. Smoothness then gives an expected descent inequality. This chapter develops a simple minibatch guarantee and shows how variance reduction can improve its sampling cost.

## Learning objectives

After this chapter, you should be able to:

- state conditional unbiasedness and a conditional variance bound for gradient estimates;
- distinguish noisy gaps from true gaps and selected-direction progress;
- prove a diameter-times-gradient-error bound for the LMO perturbation;
- derive expected objective decrease and an expected best-iterate stationarity bound;
- explain why a single stochastic gap value is not a deterministic stopping certificate;
- design Lean interfaces for filtrations, random oracle outputs, and expectation telescoping.

## 1. The stochastic constrained problem

### 1.1 Objective and information available at an iteration

Let \(\mathcal K\) be compact and convex with diameter \(D\), and consider

\[
F(x)=\mathbb E_{\xi}[f(x,\xi)].
\tag{104.1}
\]

Assume \(F\) is differentiable and \(L\)-smooth on \(\mathcal K\). At iteration \(t\), the current point \(x_t\) is determined by the past information \(\mathcal F_t\). A minibatch gradient estimate \(g_t\) satisfies

\[
\mathbb E[g_t\mid\mathcal F_t]=\nabla F(x_t),
\qquad
\mathbb E[\|g_t-\nabla F(x_t)\|_*^2\mid\mathcal F_t]
\le\frac{\sigma^2}{b}.
\tag{104.2}
\]

Here \(b\) is the batch size and \(\|\cdot\|_*\) is dual to the norm used for the domain diameter and smoothness estimate. Jensen’s inequality gives
\(\mathbb E[\|g_t-\nabla F(x_t)\|_*\mid\mathcal F_t]\le\sigma/\sqrt b\).

The stochastic Frank–Wolfe step minimizes the sampled linearization:

\[
s_t\in\arg\min_{s\in\mathcal K}\langle g_t,s\rangle,
\qquad
x_{t+1}=x_t+\gamma(s_t-x_t),
\quad \gamma\in[0,1].
\tag{104.3}
\]

The update is feasible for every sample path because it is a convex combination of feasible points. Randomness affects the chosen direction, not feasibility.

### 1.2 Three gaps that should not be conflated

The true FW gap is
\[
G_t=\max_{s\in\mathcal K}\langle\nabla F(x_t),x_t-s\rangle.
\tag{104.4}
\]
The noisy LMO returns the noisy gap
\[
\widehat G_t=\max_{s\in\mathcal K}\langle g_t,x_t-s\rangle
=\langle g_t,x_t-s_t\rangle.
\tag{104.5}
\]
The true progress along the selected direction is
\[
Q_t=\langle\nabla F(x_t),x_t-s_t\rangle.
\tag{104.6}
\]

For an exact deterministic LMO, these quantities coincide. With a stochastic gradient they need not. The atom \(s_t\) is selected to maximize the noisy linear decrease, and its true directional progress \(Q_t\) can even be negative on an individual iteration.

### 1.3 Noise perturbs the gap and the direction

Let \(e_t=g_t-\nabla F(x_t)\). For every feasible \(s\), Hölder’s inequality gives

\[
\left|\langle e_t,x_t-s\rangle\right|
\le D\|e_t\|_*.
\tag{104.7}
\]

Taking maxima over the same compact set on both sides of the noisy and true linear objectives yields

\[
|G_t-\widehat G_t|\le D\|e_t\|_*.
\tag{104.8}
\]

There is a second error when we evaluate the selected atom with the true gradient. Since \(s_t\) maximizes the noisy gap,

\[
Q_t
=\widehat G_t-\langle e_t,x_t-s_t\rangle
\ge \widehat G_t-D\|e_t\|_*
\ge G_t-2D\|e_t\|_*.
\tag{104.9}
\]

The factor two has a clear source: one perturbation changes the maximum gap value, and another evaluates the noisy maximizer under the true gradient. A small noisy gap estimates the true gap within one diameter-error term, while the selected direction’s true progress uses two.

## 2. Expected descent and stationarity

### 2.1 A one-step inequality

Smoothness of \(F\) gives

\[
F(x_{t+1})
\le F(x_t)-\gamma Q_t+\frac{L\gamma^2D^2}{2}.
\tag{104.10}
\]

Using (104.9), condition on the past and apply (104.2):

\[
\mathbb E[F(x_{t+1})\mid\mathcal F_t]
\le
F(x_t)-\gamma G_t
+\frac{2\gamma D\sigma}{\sqrt b}
+\frac{L\gamma^2D^2}{2}.
\tag{104.11}
\]

This inequality is the stochastic replacement for deterministic descent. The variance term is additive. If the batch size stays fixed while \(\gamma\) becomes small, this term can dominate the useful gap decrease.

No convexity of \(F\) is needed for (104.11). Compactness and continuity do ensure a finite minimum \(F_{\min}\), which lets us sum the decrease. For a nonconvex objective, the result is a stationarity guarantee. If \(F\) is convex, the pointwise inequality \(F(x)-F_{\min}\le G(x)\) converts the same gap bound into an objective-error bound.

### 2.2 A minibatch theorem

Assume \(F\) is \(L\)-smooth, \(\mathcal K\) has diameter \(D\), and (104.2) holds with a fixed batch size \(b\). Run (104.3) for \(T\) steps with deterministic step size \(\gamma\in(0,1]\). Let \(h_0=F(x_0)-F_{\min}\). Summing (104.11), taking expectations, and using \(F(x_T)\ge F_{\min}\) gives

\[
\frac1T\sum_{t=0}^{T-1}\mathbb E[G_t]
\le
\frac{h_0}{\gamma T}
+\frac{2D\sigma}{\sqrt b}
+\frac{L\gamma D^2}{2}.
\tag{104.12}
\]

If \(\tau\) is chosen uniformly from \(\{0,\ldots,T-1\}\) independently after the run, then

\[
\mathbb E[G_\tau]
\le
\frac{h_0}{\gamma T}
+\frac{2D\sigma}{\sqrt b}
+\frac{L\gamma D^2}{2}.
\tag{104.13}
\]

This is an expected stationarity bound for a returned iterate. It does not assert that the last iterate has small gap, and it does not give a high-probability certificate without additional concentration assumptions.

For the simple schedule \(\gamma=T^{-1/2}\), \(b=T\), the right side is

\[
\frac{h_0+2D\sigma+LD^2/2}{\sqrt T}.
\tag{104.14}
\]

The gap decreases as \(O(T^{-1/2})\), but this baseline uses \(T\) samples per round and therefore \(T^2\) gradient samples over the run. Variance-reduced estimators are motivated by reducing that sampling cost, not by changing the deterministic convex-combination update.

The three terms in (104.13) represent different bottlenecks:

- \(h_0/(\gamma T)\) is the remaining initial error after \(T\) descent steps;
- \(2D\sigma/\sqrt b\) is the stochastic direction error;
- \(L\gamma D^2/2\) is the smoothness cost of a longer move.

Reducing \(\gamma\) decreases the smoothness term but increases the transient term. Increasing \(b\) reduces the noise term but consumes more component-gradient evaluations. A useful schedule balances these terms against the accuracy and oracle budget, rather than selecting a step size in isolation.

~~~text
past samples and iterate x_t
             |
             v
       gradient estimate g_t -----> conditional error bound
             |
             v
        noisy linear oracle -----> atom s_t
             |                         |
             +------ perturbation -----+
                         |
                         v
              expected descent inequality
                         |
                         v
                  average FW gap bound
~~~

### 2.3 Expected gap is not a one-sample certificate

Equation (104.8) and the variance assumption imply
\[
\mathbb E[|G_t-\widehat G_t|\mid\mathcal F_t]
\le \frac{D\sigma}{\sqrt b}.
\tag{104.15}
\]
This controls the statistical error on average. A single observed noisy gap can still underestimate the true gap by a large amount. To stop with a deterministic guarantee, one needs a certified error bound. To stop with a probabilistic guarantee, one needs a tail assumption and a confidence-bound argument. The expected theorem (104.13) supports randomized output selection; it does not turn the raw minibatch gap into a certificate.

## 3. Two worked examples

### 3.1 A noisy gradient can select an ascent direction

Let \(\mathcal K\) be the two-dimensional simplex with vertices \(e_1,e_2\), current point \(x=(1/2,1/2)\), and true gradient \(\nabla F(x)=(0,1)\). The exact LMO chooses \(e_1\), and the true gap is \(G=1/2\).

Suppose a noisy estimate is \(g=(1,0)\). Its LMO chooses \(s=e_2\), and the noisy gap is \(\widehat G=1/2\), so the sampled gap looks positive and plausible. But the selected direction has true progress

\[
Q=\langle(0,1),(1/2,-1/2)\rangle=-1/2.
\]

The update moves uphill for the true objective. This does not contradict the expected theorem: the estimator noise is large on this sample, and (104.9) explicitly permits negative one-step progress. Averaging and controlling the error term is essential.

### 3.2 Read the minibatch bound numerically

Suppose \(h_0=1\), \(D=1\), \(L=1\), \(\sigma=1\), \(T=100\), and \(b=100\). With \(\gamma=0.1\), the three terms in (104.13) are \(0.1\), \(0.2\), and \(0.05\), respectively. A uniformly sampled iterate therefore satisfies

\[
\mathbb E[G_\tau]\le0.35.
\]

The variance term is the largest contribution here. Increasing the number of outer steps while holding \(b\) fixed eventually leaves a noise floor. To improve the bound, one can increase the batch, reduce estimator variance, or change the step schedule; merely running more iterations is not enough.

## 4. Variance reduction and finite sums

### 4.1 Finite-sum gradients

For
\[
F(x)=\frac1n\sum_{i=1}^n f_i(x),
\]
a minibatch samples component gradients. If indices are uniform and independent, the sample average is conditionally unbiased and the variance term in (104.2) typically decreases as \(1/b\). For without-replacement sampling, the variance has a finite-population correction; the proof should use the exact sampling law rather than assume independent draws.

Full-gradient Frank–Wolfe performs \(n\) component-gradient evaluations per iteration but gives an exact LMO direction. Minibatch Frank–Wolfe reduces per-iteration gradient cost but introduces direction noise. The comparison should count component-gradient evaluations and linear-oracle calls separately.

### 4.2 Control variates change the error term

A control-variate estimator can reuse a reference gradient and correct it with a sampled difference. The resulting estimator may be unbiased with much smaller conditional variance near the reference point. In the proof above, this improves \(\sigma/\sqrt b\) without changing the feasible update or curvature lemma.

Some modern analyses permit biased estimators and instead assume a recursion for estimator error. In that setting, replace conditional unbiasedness by a bound on both the conditional bias and variance. The one-step proof then contains an additional term
\(2\gamma D\|\mathbb E[e_t\mid\mathcal F_t]\|_*\). The filtration and estimator state must be included explicitly; it is not valid to remove this term by saying the estimator is approximately unbiased.

### 4.3 A Lyapunov state for momentum

Momentum estimators carry information from earlier gradients, so \(g_t\) is not conditionally unbiased for the current gradient in every method. Their useful property is often a recursion of the form
\[
\mathbb E[\|g_t-\nabla F(x_t)\|_*^2]
\le a_t\,\mathbb E[\|g_{t-1}-\nabla F(x_{t-1})\|_*^2]
+b_t\,\mathbb E[\|x_t-x_{t-1}\|^2]+c_t.
\]
The estimator error then becomes part of a Lyapunov quantity together with objective error or accumulated stationarity gaps. The deterministic perturbation estimate (104.9) remains valid at each iteration; what changes is the proof used to sum the noise terms.

For formalization, carry the estimator state in the algorithm state and prove its error recursion independently. A final expected-gap theorem can consume a bound on \(\sum_t\gamma_t\mathbb E\|e_t\|_*\). This keeps the FW geometry unchanged and localizes method-specific work to a stochastic-estimator module. Chapter 96’s control-variate decomposition provides the relevant proof pattern.

## 5. Lean proof architecture

### 5.1 Make the filtration part of the theorem

Model the current iterate as measurable with respect to \(\mathcal F_t\), and state conditional unbiasedness and conditional second-moment bounds relative to that sigma-algebra. Keep the sampled gradient \(g_t\), selected atom \(s_t\), and true gradient \(\nabla F(x_t)\) distinct in the theorem statement. If the sample space is finite, conditional expectations can reduce to finite weighted sums; for general probability spaces, use the conditional-expectation API from Chapters 35–36.

An unconditional statement such as \(\mathbb E[g_t]=\mathbb E[\nabla F(x_t)]\) is not a substitute for conditional unbiasedness when \(x_t\) depends on earlier samples. The iterate and the next batch are coupled through the history, so the one-step argument must condition on that history before taking expectations. Likewise, choosing the output index after inspecting noisy gaps introduces selection bias; the simple average identity in (104.13) uses an independent uniform index.

Feasibility is a pathwise theorem: \(x_t,s_t\in\mathcal K\) and \(\gamma\in[0,1]\) imply \(x_{t+1}\in\mathcal K\). It should not be hidden inside an almost-sure statement if it holds for every outcome.

### 5.2 Isolate the deterministic perturbation lemma

Prove a lemma for arbitrary vectors \(g,\nabla\), a feasible point \(x\), and a point \(s\) minimizing the linear objective defined by \(g\). It should return:

- a bound on the difference between the true and noisy maximum gaps;
- a lower bound on the true progress of the noisy-selected atom.

This lemma uses only oracle optimality, the diameter bound, and Hölder’s inequality. It contains no expectations, filtration, or smoothness. The stochastic proof can then apply conditional expectation to a deterministic inequality.

### 5.3 Telescope before choosing the output

Condition (104.11) on the past, take total expectations, and sum over \(t\). The objective terms telescope. Rearrange the resulting inequality into a sum of expected gaps, then divide by \(T\) and introduce an independent uniform index \(\tau\). This ordering makes the proof’s probabilistic dependencies visible.

For a Lean result that returns an actual iterate, carry \(\tau\) as data. A separate theorem proves the expectation bound for the indexed family. If a stopping rule uses noisy gaps, its proof should include either an error bar or a concentration event; the expected average-gap theorem does not justify stopping whenever one sampled gap happens to be small.

## 6. Common failure modes

1. **Treating the noisy atom as unbiased.** The LMO is nonlinear, so an unbiased gradient does not produce an unbiased atom.
2. **Using the noisy gap as the true gap.** Their difference is bounded by gradient error times diameter.
3. **Assuming the selected direction always descends.** Its true progress may be negative on an individual sample.
4. **Ignoring the second perturbation term.** The true gap and the true progress of the noisy maximizer differ by up to two diameter-error terms.
5. **Claiming feasibility only in expectation.** Convex-combination feasibility holds pathwise.
6. **Forgetting the batch-size floor.** Fixed variance and a vanishing step can leave a nonzero expected-gap floor.
7. **Calling the average-gap bound a last-iterate result.** It supports a uniformly sampled or best-certified iterate.
8. **Using an expected bound as a confidence interval.** High-probability stopping requires stronger tail information.
9. **Combining linear-oracle cost with gradient-sample cost.** They are separate oracle resources.
10. **Dropping estimator bias.** A biased estimator needs an explicit bias term or a recursion controlling it.

## 7. Exercises

1. Prove that the stochastic update remains in \(\mathcal K\) for every realization of \(g_t\).
2. Derive (104.8) from the diameter bound and the maximum representation of the FW gap.
3. Prove the true-direction estimate (104.9), identifying both uses of the noise norm.
4. Starting from smoothness, derive the conditional expected descent inequality (104.11).
5. Sum (104.11) and prove (104.12).
6. Show that a uniform independent output index has expected gap equal to the average expected gap.
7. For the simplex example, compute the true gap, noisy gap, and selected-direction progress.
8. Derive the minibatch variance bound for sampling \(b\) independent component gradients.
9. Add a conditional bias bound and state the modified version of (104.11).
10. Compare the total component-gradient evaluations for full-gradient FW and the schedule \(b=T\).
11. State Lean structures for the filtration, gradient estimator certificate, and noisy LMO certificate.
12. Explain why an observed gap of zero under one stochastic sample does not certify exact stationarity.

## 8. Chapter summary

Stochastic Frank–Wolfe preserves feasibility pathwise, but a noisy gradient changes the atom selected by the linear oracle. The noisy gap, true gap, and true progress along the sampled direction are distinct. Diameter and dual-norm error bounds relate them, while smoothness turns that relation into an expected descent inequality.

Summing conditional expected decreases gives an expected average-gap guarantee and a uniformly sampled output with \(O(T^{-1/2})\) stationarity under a simple minibatch schedule. The result depends on both outer step size and estimator variance. In Lean, isolate pathwise feasibility, deterministic oracle perturbation, conditional expectation, and finite telescoping before analyzing variance-reduced special cases.

## Further reading

- Nazykov et al., [“Stochastic Frank-Wolfe: Unified Analysis and Zoo of Special Cases”](https://proceedings.mlr.press/v238/nazykov24a.html), for a unified framework covering unbiased and biased stochastic estimators.
- Negiar et al., [“Stochastic Frank-Wolfe for Constrained Finite-Sum Minimization”](https://proceedings.mlr.press/v119/negiar20a.html), for variance reduction and stochastic gap estimation in finite-sum problems.
- Chapter 103 — Nonconvex Frank–Wolfe and Stationarity Certificates, for the deterministic nonconvex gap theorem.
- Chapters 95–96, for conditional stochastic-gradient bounds and control-variate proof patterns.

