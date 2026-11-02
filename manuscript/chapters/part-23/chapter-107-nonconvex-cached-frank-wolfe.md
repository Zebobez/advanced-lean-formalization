# Chapter 107 — Nonconvex Stationarity with Cached Frank–Wolfe Gradients

> **Audience.** This chapter extends the cached-gradient method from Chapter 106 to nonconvex generalized linear objectives. It assumes the reader knows the Frank–Wolfe gap, the stale-table recurrence, and the smoothness descent lemma. The central question is what can still be proved when objective convexity is removed.

For a convex objective, the Frank–Wolfe gap controls suboptimality. For a nonconvex objective, that interpretation disappears: a point can have zero gap while being far from a global minimizer. The gap remains useful as a constrained first-order stationarity measure, and smoothness still converts directional progress into objective decrease.

The cached derivative table from Chapter 106 does not rely on convexity. Its error shrinks because coordinates are refreshed and the objective moves gradually, not because the loss is convex. This chapter combines that error recursion with a nonconvex descent inequality. The result is an asymptotic expected-stationarity guarantee and a finite-horizon bound for a step-size-weighted random iterate.

## Learning objectives

After this chapter, you should be able to:

- define constrained first-order stationarity using the Frank–Wolfe gap;
- show why the gap no longer bounds objective suboptimality for nonconvex functions;
- derive a descent inequality using the cached stochastic gap and table error;
- prove a finite weighted-gap bound from a lower bound on the objective;
- explain the assumptions behind an asymptotic expected-stationarity conclusion;
- formalize the analytic and stochastic layers separately in Lean.

## 1. Stationarity without convexity

### 1.1 The constrained first-order condition

Let \(\mathcal C\subseteq\mathbb R^d\) be compact and convex, and let \(F\) be differentiable on a neighborhood of \(\mathcal C\). The Frank–Wolfe gap at \(w\in\mathcal C\) is

\[
G(w)=\max_{s\in\mathcal C}\langle\nabla F(w),w-s\rangle.
\tag{107.1}
\]

Because \(s=w\) is feasible, \(G(w)\ge0\). Its vanishing is equivalent to
\[
\langle\nabla F(w),s-w\rangle\ge0
\quad\text{for every }s\in\mathcal C.
\tag{107.2}
\]
This is the first-order variational inequality for a constrained stationary point. It includes boundary points: the gradient need not vanish in the ambient space if all feasible directions have nonnegative directional derivative.

If \(F\) is convex, the supporting-hyperplane inequality yields
\(F(w)-F(w^\star)\le G(w)\). Without convexity, that inequality is unavailable. Chapter 103 introduced the nonconvex gap as a stationarity measure; here we analyze it under a stochastic finite-sum gradient state.

### 1.2 A zero gap can occur away from a minimizer

Consider
\[
F(w)=\left(w^2-\frac14\right)^2,\qquad \mathcal C=[-1,1].
\tag{107.3}
\]
At \(w=0\), the derivative is zero, so \(G(0)=0\). But
\[
F(0)=\frac1{16},\qquad F\left(\frac12\right)=0.
\tag{107.4}
\]
Thus zero FW gap certifies first-order stationarity, not global optimality. In this example \(w=0\) is a local maximum. A nonconvex convergence theorem must therefore report gap or stationarity, not objective suboptimality.

Compactness and continuity do give a finite lower bound \(F_{\min}=\min_{w\in\mathcal C}F(w)\). That lower bound is enough to telescope descent inequalities. It does not restore convexity or make a stationary point globally optimal.


## 2. Nonconvex cached-gradient Frank–Wolfe

### 2.1 Retain the finite-sum structure

Use the generalized linear model from Chapter 106:
\[
F(w)=\psi(Xw),\qquad
\psi(z)=\frac1n\sum_{i=1}^n\phi_i(z_i).
\tag{107.5}
\]
Assume each scalar loss derivative is \(L\)-Lipschitz; the losses need not be convex. Then \(\nabla\psi\) is \(L/n\)-Lipschitz in Euclidean norm, and for feasible \(u,v\),
\[
F(u)\le F(v)+\langle\nabla F(v),u-v\rangle
+\frac{L}{2n}\|X(u-v)\|_2^2.
\tag{107.6}
\]

Maintain the table \(\alpha_t\), aggregate \(r_t=X^\top\alpha_t\), and point \(w_t\). Sample one data index, refresh its table coordinate at the current point, update \(r_t\) incrementally, call the LMO, and take a convex-combination step. Define
\[
H_t=\|\alpha_t-\nabla\psi(Xw_{t-1})\|_1,\quad
D_2=\max_{u,v\in\mathcal C}\|X(u-v)\|_2,\quad
D_\infty=\max_{u,v\in\mathcal C}\|X(u-v)\|_\infty.
\tag{107.7}
\]
The error recursion from Chapter 106 remains valid without convexity. For \(t\ge2\), it reads
\[
\mathbb E_t H_t\le
\left(1-\frac1n\right)
\left(H_{t-1}+\frac{L\gamma_{t-1}D_1}{n}\right).
\tag{107.8}
\]
Uniform coordinate refresh and component smoothness establish this relation; convexity is not used. At the first refresh, \(H_1\le H_0\) because the sampled coordinate is made exact at \(w_0\) and the other coordinates have not moved.

### 2.2 True and cached gaps

At iteration \(t\), let \(s_t\) minimize the cached linear objective:
\[
s_t\in\arg\min_{s\in\mathcal C}\langle r_t,s\rangle,\qquad
w_t=(1-\gamma_t)w_{t-1}+\gamma_t s_t.
\tag{107.9}
\]
Define the cached gap
\[
\widehat G_t=\max_{s\in\mathcal C}
\langle r_t,w_{t-1}-s\rangle
=\langle r_t,w_{t-1}-s_t\rangle.
\tag{107.10}
\]
The true gap \(G_t=G(w_{t-1})\) uses
\(\nabla F(w_{t-1})=X^\top\nabla\psi(Xw_{t-1})\). By the \(\ell_1\)-\(\ell_\infty\) pairing and the mapped diameter,
\[
|G_t-\widehat G_t|\le D_\infty H_t.
\tag{107.11}
\]
This is a deterministic statewise inequality. The cached gap is nonnegative because \(w_{t-1}\in\mathcal C\) is one of the points in the maximum.

### 2.3 Descent uses the gap, not convexity

Apply (107.6) with \(u=w_t\), \(v=w_{t-1}\). Since
\(w_t-w_{t-1}=\gamma_t(s_t-w_{t-1})\), smoothness contributes at most
\(L\gamma_t^2D_2^2/(2n)\). The true directional decrease differs from the cached gap by at most \(D_\infty H_t\):
\[
\langle\nabla F(w_{t-1}),w_{t-1}-s_t\rangle
\ge \widehat G_t-D_\infty H_t.
\tag{107.12}
\]
Consequently,
\[
F(w_t)\le F(w_{t-1})-\gamma_t\widehat G_t
+\gamma_tD_\infty H_t
+\frac{L\gamma_t^2D_2^2}{2n}.
\tag{107.13}
\]
No convexity appears in this argument. Convexity was needed in Chapter 106 to replace a gradient inner product by a primal objective gap. Here we keep the linear gap itself.

The distinction is useful in Lean: (107.13) is an analytic theorem about a smooth objective, a feasible update, and an approximate LMO. It should not assume an optimizer or a convexity typeclass. A later corollary can add convexity and convert the result into a suboptimality theorem, but the nonconvex lemma should remain general.


## 3. Telescoping a nonconvex stationarity bound

### 3.1 The finite weighted inequality

Sum (107.13) over \(t=1,\ldots,T\). The objective terms telescope. Since
\(F(w_T)\ge F_{\min}\),
\[
\sum_{t=1}^T\gamma_t\widehat G_t
\le F(w_0)-F_{\min}
+D_\infty\sum_{t=1}^T\gamma_tH_t
+\frac{LD_2^2}{2n}\sum_{t=1}^T\gamma_t^2.
\tag{107.14}
\]
Apply (107.11) in the direction \(G_t\le\widehat G_t+D_\infty H_t\) and combine:
\[
\sum_{t=1}^T\gamma_t G_t
\le F(w_0)-F_{\min}
+2D_\infty\sum_{t=1}^T\gamma_tH_t
+\frac{LD_2^2}{2n}\sum_{t=1}^T\gamma_t^2.
\tag{107.15}
\]
The two error sums have different origins. One accounts for using the cached LMO direction in objective descent; the other transfers the cached gap to the true gap.

Take expectations and suppose the step sizes are deterministic and positive. If an output time \(\tau\) is sampled independently after the run with
\[
\Pr(\tau=t)=\frac{\gamma_t}{A_T},\qquad
A_T=\sum_{t=1}^T\gamma_t,
\tag{107.16}
\]
then
\[
\mathbb E[G_\tau]\le
\frac{
F(w_0)-F_{\min}
+2D_\infty\sum_{t=1}^T\gamma_t\mathbb E H_t
+\frac{LD_2^2}{2n}\sum_{t=1}^T\gamma_t^2
}{A_T}.
\tag{107.17}
\]
This is a finite-horizon expected stationarity statement. It concerns a weighted random iterate, not necessarily the last iterate.

### 3.2 A diminishing-step schedule

Choose \(\gamma_t=2/(t+2)\). Then \(\sum_t\gamma_t\) diverges logarithmically, while \(\sum_t\gamma_t^2\) converges. The stale-table recurrence (107.8) gives \(\mathbb E H_t=O(1/t)\), with constants depending on the initialization and data geometry. Hence
\[
\sum_t\gamma_t\,\mathbb E H_t<\infty.
\tag{107.18}
\]
The numerator in (107.17) is bounded uniformly in \(T\), and \(A_T\) grows on the order of \(\log T\). This gives the direct, though conservative, weighted-output guarantee
\[
\mathbb E[G_\tau]=O(1/\log T).
\tag{107.19}
\]
The analysis also implies
\[
\liminf_{t\to\infty}\mathbb E[G_t]=0.
\tag{107.20}
\]
Indeed, if the expected gaps stayed above a positive constant eventually, their sum weighted by a divergent harmonic step sequence would diverge, contradicting (107.15) and the finite error budget.

This guarantee is weaker than the familiar finite-time \(O(T^{-1/2})\) stationarity bounds obtained for some stochastic methods with other step and batch schedules. Its value is structural: it shows that the cached estimator’s error vanishes quickly enough for the FW descent argument to force stationarity along a subsequence, while using one sampled component per iteration. The theorem does not say that every iterate converges, that the last iterate has small gap, or that the algorithm reaches a global minimizer.

### 3.3 A schedule criterion beyond the harmonic example

The telescope does not fundamentally require the specific sequence \(2/(t+2)\). For a deterministic step schedule, a sufficient set of conditions is
\[
\sum_{t=1}^{\infty}\gamma_t=\infty,\qquad
\sum_{t=1}^{\infty}\gamma_t^2<\infty,\qquad
\sum_{t=1}^{\infty}\gamma_t\mathbb E H_t<\infty.
\tag{107.21}
\]
The first condition prevents the total weight assigned to descent from staying finite. The second makes the accumulated smoothness cost finite. The third ensures that approximate-oracle error does not consume an unbounded amount of that descent budget. Under these assumptions, the numerator of (107.17) stays bounded while its denominator diverges, so the expected gap of the weighted random output tends to zero.

The estimator recurrence links the third condition to the step schedule. With \(q=1-1/n\), its unconditional form for \(t\ge2\) is
\[
\mathbb E H_t\le q\,\mathbb E H_{t-1}
+q\frac{LD_1}{n}\gamma_{t-1}.
\tag{107.22}
\]
Repeated substitution gives a geometrically weighted sum of recent step sizes plus a decaying initialization term. When the step sizes decrease slowly compared with the fixed refresh time scale \(n\), the tracking error follows their scale after an initial transient. For \(\gamma_t\asymp t^{-a}\) with \(1/2<a<1\), this yields \(\mathbb E H_t=O(t^{-a})\) under the corresponding recurrence bound. Then both \(\sum\gamma_t^2\) and \(\sum\gamma_t\mathbb E H_t\) converge, while \(A_T\) grows like \(T^{1-a}\). The weighted-output argument gives a finite-horizon expected gap of order \(T^{-(1-a)}\).

This calculation exposes a tradeoff. Taking \(a\) close to \(1/2\) makes the total weight grow quickly, but makes the summable squared-step budget approach its boundary. Taking \(a=1\), as in the paper’s schedule, gives only logarithmic total weight and the conservative \(O(1/\log T)\) bound from this generic telescope. Sharper rates may require a different estimator, more structure, a different output rule, or a tighter analysis. A constant step size violates square summability, so this argument alone cannot establish asymptotic stationarity for it.

### 3.4 Worked example: evaluate the gap budget

Suppose the initial objective range is bounded by \(1\), and for a finite horizon the two accumulated error contributions satisfy
\[
2D_\infty\sum_{t=1}^T\gamma_t\mathbb E H_t=0.2,\qquad
\frac{LD_2^2}{2n}\sum_{t=1}^T\gamma_t^2=0.5.
\tag{107.23}
\]
If \(A_T=3.2\), (107.17) gives
\[
\mathbb E[G_\tau]\le\frac{1+0.2+0.5}{3.2}\approx0.532.
\tag{107.24}
\]
The number is an upper bound for a weighted randomly selected iterate. It is not a bound for \(G_T\). To improve it, one must reduce curvature or estimator error, or increase the total step weight while preserving the summability conditions used in the proof.

## 4. Interpret the stationarity theorem carefully

### 4.1 Boundary stationarity and feasible directions

The condition \(G(w)=0\) means every feasible chord from \(w\) has nonnegative directional derivative. At a boundary point, this can hold even when \(\nabla F(w)\ne0\). For example, on \(\mathcal C=[0,1]\) with \(F(w)=w\), the minimizer \(w=0\) has derivative 1 but gap
\[
G(0)=\max_{s\in[0,1]}(0-s)=0.
\tag{107.25}
\]
A theorem that tries to prove \(\|\nabla F(w_t)\|\to0\) would be false for constrained FW. The gap is the correct certificate because it includes the geometry of the feasible set.

### 4.2 Expected subsequences are not pathwise convergence

The conclusion \(\liminf_t\mathbb E[G_t]=0\) is weaker than almost-sure convergence of \(G_t\), and weaker than \(\mathbb E[G_t]\to0\). A sequence may have occasional large values while its lower limit is zero. The finite-horizon bound (107.17) offers a practical alternative: return an independent weighted sample and state its expected gap guarantee.

If a stopping rule observes the cached gap \(\widehat G_t\), then (107.11) says the error is controlled by \(D_\infty H_t\). An expected bound on \(H_t\) gives an expected discrepancy; it does not by itself certify a particular run. A high-probability statement needs a tail argument or a conservative Markov bound with known constants. Chapters 105–106 explain why the distinction matters for stochastic gap estimates.

### 4.3 Nonconvex objectives still need a finite lower bound

The descent telescope uses \(F(w_T)\ge F_{\min}\). Compactness of \(\mathcal C\) and continuity of \(F\) provide this bound. Without a lower bound, a sum of positive gaps might be paid for by objective values decreasing without limit. Strong convexity is unnecessary, but boundedness below is not optional.

For generalized linear models on compact domains, smooth component losses ensure that \(F\) is smooth and continuous, so the assumption is natural. In a formal theorem, it can be passed as an explicit scalar bound rather than deriving compactness and existence of a minimizer inside the stochastic proof.


## 5. Lean proof architecture

### 5.1 Make the nonconvex lemma independent of convexity

The core one-step theorem should assume only:

- \(w_{t-1},s_t\in\mathcal C\);
- a step size \(\gamma_t\in[0,1]\);
- the smoothness inequality for \(F\);
- an approximate-oracle certificate relating the true directional decrease to \(\widehat G_t\) and \(H_t\).

It should conclude (107.13). Do not require a minimizer, convexity, or an objective gap. Those belong in a corollary for convex objectives.

### 5.2 Keep finite summation deterministic

First prove a scalar theorem of the form: if
\[
a_t\le a_{t-1}-b_t+c_t,
\]
then \(\sum_{t\le T}b_t\le a_0-a_T+\sum_{t\le T}c_t\). Instantiate it with
\(a_t=F(w_t)\), \(b_t=\gamma_t\widehat G_t\), and
\(c_t=\gamma_tD_\infty H_t + LD_2^2\gamma_t^2/(2n)\).
A separate lemma transfers \(\widehat G_t\) to \(G_t\). This keeps the objective telescope free of gap-maximization details.

### 5.3 Separate probability and output selection

The conditional error recurrence should be proved relative to the history before the newly sampled index. A distinct theorem then takes total expectations and establishes \(\sum\gamma_t\mathbb E H_t<\infty\). Finally, define the output distribution on the finite time index and use the finite weighted-average identity. This avoids encoding a random stopping index inside the descent induction.

The proof-state pipeline is:

~~~text
smoothness and cached LMO
          |
          v
one-step decrease with H_t
          |
          +---- coordinate-refresh recurrence
          |               |
          |               v
          |       summable weighted error
          v
finite objective telescope
          |
          v
weighted expected FW-gap bound
          |
          v
randomized stationarity output
~~~

For a Lean library, the theorem should expose the guarantee level in its name or documentation: expected weighted gap, lower-limit expected gap, and almost-sure convergence are different results.


## 6. Common failure modes

1. **Converting gap to objective error without convexity.** The quartic example has zero gap at a non-minimizer.
2. **Demanding zero ambient gradient at a boundary solution.** Constrained stationarity is a variational inequality.
3. **Using the convex recurrence \((1-\gamma_t)\varepsilon_{t-1}\).** That step relies on convexity and is unavailable here.
4. **Dropping one of the two table-error terms.** One enters descent; the other compares cached and true gaps.
5. **Claiming the last iterate is stationary.** The theorem gives a lower-limit or weighted-output result.
6. **Claiming almost-sure convergence from an expectation bound.** A separate martingale or concentration argument would be required.
7. **Ignoring lower boundedness.** The objective telescope needs a finite lower bound.
8. **Using a constant step size with nonvanishing error.** Then the weighted noise and curvature budgets may diverge.
9. **Treating the cached gap as exact.** Its difference is bounded by \(D_\infty H_t\).
10. **Confusing computational and iteration complexity.** One sampled component per step does not make the rate constant independent of the data geometry.

## 7. Exercises

1. Prove the equivalence between zero FW gap and the variational inequality (107.2).
2. Compute the FW gap of \(F(w)=(w^2-\tfrac14)^2\) at \(w=0\) and compare it with the global objective gap.
3. Derive the nonconvex descent inequality (107.13) using only smoothness and the cached LMO.
4. Starting from (107.11), derive (107.15) from the one-step telescope.
5. Show that \(\gamma_t=2/(t+2)\) has divergent sum and square-summable squares.
6. Use the recurrence (107.8) to explain why expected table error is \(O(1/t)\) for this schedule.
7. Prove the weighted-output identity for \(\tau\) sampled with probabilities \(\gamma_t/A_T\).
8. Give a nonconvex example where a boundary point is stationary although the ambient gradient is nonzero.
9. Explain why \(\liminf_t\mathbb E[G_t]=0\) does not imply \(\mathbb E[G_t]\to0\).
10. State the extra information required to turn an expected cached-gap error into a high-probability stopping rule.
11. Design Lean theorem boundaries for smooth descent, gap discrepancy, stochastic error summability, and output sampling.
12. Identify the exact line of a convex FW proof that must be replaced when deriving a nonconvex stationarity result.

## 8. Chapter summary

Nonconvex Frank–Wolfe cannot use the gap as an objective-suboptimality bound, but the gap remains the right constrained stationarity measure. Smoothness gives descent along the cached LMO direction, with an additive term proportional to stale-table error. The estimator recurrence from Chapter 106 remains valid because it depends on coordinate refresh and smoothness, not loss convexity.

A finite telescope controls the step-size-weighted gaps. With a diminishing schedule whose total weight diverges, squared steps are summable, and weighted estimator errors are summable, a weighted random iterate has a vanishing expected gap. For the cached method’s harmonic schedule, this yields an asymptotic lower-limit result and a conservative logarithmic finite-horizon bound. The guarantee is expected stationarity, not last-iterate, pathwise, or global-optimality convergence.

## Further reading

- Negiar et al., [“Stochastic Frank-Wolfe for Constrained Finite-Sum Minimization”](https://proceedings.mlr.press/v119/negiar20a.html), for the nonconvex asymptotic stationarity analysis of the cached estimator.
- Chapters 103–106, for nonconvex gap geometry, stochastic descent, finite-sum variance reduction, and the generalized-linear cached-gradient state.

