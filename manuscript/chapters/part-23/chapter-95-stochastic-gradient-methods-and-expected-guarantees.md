# Chapter 95 — Stochastic Gradient Methods and Expected Guarantees

> **Audience.** This chapter assumes the convex analysis and probability foundations developed earlier in the book, especially Chapters 34–44 and 90–94. It studies gradient updates driven by random samples and formalizes the distinction between an expected guarantee and a statement about every sample path.

Deterministic gradient methods use the exact derivative of an objective at every step. That is often too expensive when the objective is an expectation or a sum with a very large number of terms. Stochastic gradient methods replace the full derivative by a sampled estimate. One update is cheaper, but the estimate has noise, so the proof must track conditional expectations and accumulated variance.

The main theorem below is the projected stochastic subgradient bound for a convex objective. Its proof is a one-step projection inequality, conditional unbiasedness, and a finite telescoping sum. Later sections show how smoothness exposes the noise floor, how mini-batches reduce variance, and why a constant step size may leave the iterates fluctuating around the minimizer.

## Learning objectives

After this chapter, you should be able to:

- specify a stochastic gradient oracle using conditional rather than unconditional unbiasedness;
- prove an expected \(O(T^{-1/2})\) objective bound for projected stochastic subgradient descent;
- distinguish a bounded second moment from a bounded variance assumption;
- derive a stationarity estimate for smooth objectives under additive gradient noise;
- calculate how independent mini-batching changes the variance term;
- design Lean interfaces that isolate projection geometry, conditional expectation, and finite-horizon summation.

## 1. The objective and the stochastic oracle

Let \(C\) be a nonempty closed convex subset of a finite-dimensional real inner-product space. The goal is to minimize a convex function \(F:C\to\mathbb R\). In many applications \(F\) is an expectation,

\[
F(x)=\mathbb E_{\xi}[f(x;\xi)],
\tag{95.1}
\]

or a finite average,

\[
F(x)=\frac1n\sum_{i=1}^n f_i(x).
\tag{95.2}
\]

Computing \(\nabla F(x)\) may require an integral or all \(n\) component gradients. A stochastic oracle returns a random vector \(g_t\) at the current iterate \(x_t\). The algorithm updates using \(g_t\) rather than evaluating \(\nabla F(x_t)\).

### 1.1 Conditional unbiasedness is the right assumption

Let \(\mathcal F_t\) describe all information available before the sample for round \(t\) is drawn. The iterate \(x_t\) is assumed to be \(\mathcal F_t\)-measurable. In the differentiable case, require

\[
\mathbb E[g_t\mid\mathcal F_t]=\nabla F(x_t).
\tag{95.3}
\]

All conditional equalities, inclusions, and inequalities in this chapter are understood to hold almost surely.

For a nonsmooth convex objective, the conditional mean may instead be a subgradient:

\[
\mathbb E[g_t\mid\mathcal F_t]\in\partial F(x_t).
\tag{95.4}
\]

Conditional unbiasedness permits adaptive iterates: the next query point depends on all earlier samples. An unconditional identity such as \(\mathbb E[g_t]=\mathbb E[\nabla F(x_t)]\) does not by itself justify the one-step proof, because it does not say how the sample correlates with the current iterate.

When \(g_t\) is formed by differentiating a sampled loss, the identity \(\mathbb E[\nabla f(x;\xi)]=\nabla\mathbb E[f(x;\xi)]\) also needs an analytic justification, such as a suitable integrable bound on the derivatives. It is useful to state the oracle condition (95.3) directly unless the development actually needs to prove it from a sample model. This keeps interchange-of-limit arguments out of the optimization theorem.

The basic convex theorem will use a uniform second-moment bound

\[
\mathbb E[\|g_t\|^2\mid\mathcal F_t]\le G^2.
\tag{95.5}
\]

This is stronger than saying the variance is at most \(G^2\). If \(g_t\) is an unbiased estimate of a nonzero gradient, then

\[
\mathbb E[\|g_t\|^2\mid\mathcal F_t]
=\|\nabla F(x_t)\|^2+
\mathbb E[\|g_t-\nabla F(x_t)\|^2\mid\mathcal F_t].
\tag{95.6}
\]

The second term is the conditional variance; the first is the squared signal. A variance bound alone does not bound the full second moment unless the signal is also controlled.

### 1.2 A finite-sum oracle

For (95.2), sample \(I_t\) uniformly from \(\{1,\ldots,n\}\), independently of the past, and set \(g_t=\nabla f_{I_t}(x_t)\). Linearity of a finite sum gives

\[
\mathbb E[g_t\mid\mathcal F_t]
=\frac1n\sum_{i=1}^n\nabla f_i(x_t)
=\nabla F(x_t).
\]

The sample replaces \(n\) gradient evaluations with one. Its conditional variance is

\[
\frac1n\sum_{i=1}^n
\|\nabla f_i(x_t)-\nabla F(x_t)\|^2.
\tag{95.7}
\]

Even at an unconstrained minimizer of \(F\), this quantity need not vanish: the component gradients can cancel in their average while remaining individually nonzero. This explains why plain stochastic gradient descent can continue to move after reaching the empirical optimum.

For a finite example, let an oracle return either component gradient `−1` or `+1` with equal weight. Its expected gradient is zero, but its second moment and variance are both one. Thus a vanishing full gradient does not imply that individual stochastic updates stop moving.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def sampledNoise : State → Int := fun s => if s = zero then -1 else 1

theorem sampled_noise_has_zero_mean :
    expectationNumerator uniformWeight sampledNoise = 0 := by decide

theorem sampled_noise_second_moment :
    expectationNumerator uniformWeight (fun s => sampledNoise s ^ 2) = 2 := by decide

theorem sampled_noise_variance_is_one :
    ((expectationNumerator uniformWeight (fun s => sampledNoise s ^ 2) : Int) : ℚ) / 2 -
      (((expectationNumerator uniformWeight sampledNoise : Int) : ℚ) / 2) ^ 2 = 1 := by
  rw [sampled_noise_second_moment, sampled_noise_has_zero_mean]
  norm_num
```

## 2. Projected stochastic subgradient descent

Start from a fixed \(x_1\in C\). Given a step size \(\eta>0\), define

\[
x_{t+1}=P_C(x_t-\eta g_t),
\tag{95.8}
\]

where \(P_C\) is the Euclidean projection onto \(C\). The projection keeps every iterate feasible. The proof uses a deterministic inequality valid for each realization of \(g_t\), before taking expectations.

### 2.1 The projection certificate

For any fixed comparator \(u\in C\), nonexpansiveness of projection and \(P_C(u)=u\) imply

\[
\|x_{t+1}-u\|^2
\le\|x_t-\eta g_t-u\|^2.
\]

Expand the right-hand side and rearrange:

\[
2\eta\langle g_t,x_t-u\rangle
\le\|x_t-u\|^2-\|x_{t+1}-u\|^2
+\eta^2\|g_t\|^2.
\tag{95.9}
\]

This is the same potential inequality used in deterministic projected subgradient descent. Randomness enters only when the inequality is averaged.

### 2.2 One round in expectation

Because \(x_t\) and \(u\) are known given \(\mathcal F_t\), conditional expectation pulls them out of the inner product. Use (95.4) and the subgradient inequality

\[
F(x_t)-F(u)
\le\left\langle\mathbb E[g_t\mid\mathcal F_t],x_t-u\right\rangle.
\]

Taking conditional expectations in (95.9), then using (95.5), yields

\[
2\eta\,\mathbb E[F(x_t)-F(u)]
\le
\mathbb E[\|x_t-u\|^2-\|x_{t+1}-u\|^2]
+\eta^2G^2.
\tag{95.10}
\]

The displayed form takes full expectation; the same argument first gives a conditional inequality. Integrability is needed to make each conditional expectation well-defined.

There is no independence factorization in this step. The random vector \(g_t\) can be correlated with the past through the adaptive query point; conditional unbiasedness handles precisely that dependence. The terminal squared distance is not independent of the history either, so it remains inside the expectation until the telescoping sum is formed.

### 2.3 Telescope and average

Sum (95.10) from \(t=1\) to \(T\). All intermediate squared distances cancel:

\[
2\eta\sum_{t=1}^T\mathbb E[F(x_t)-F(u)]
\le \|x_1-u\|^2-\mathbb E\|x_{T+1}-u\|^2
+\eta^2G^2T.
\]

Drop the nonnegative final distance and define the average prediction

\[
\bar x_T=\frac1T\sum_{t=1}^T x_t.
\]

Since \(C\) is convex, \(\bar x_T\in C\) for every sample path. Jensen's inequality applies pathwise and then in expectation. Writing \(D=\|x_1-u\|\), we obtain

\[
\mathbb E[F(\bar x_T)-F(u)]
\le\frac{D^2}{2\eta T}+\frac{\eta G^2}{2}.
\tag{95.11}
\]

Choose \(u\) to be a minimizer of \(F\) on \(C\). If \(D>0\), \(G>0\), and \(T\ge1\), the choice \(\eta=D/(G\sqrt T)\) balances the two terms:

\[
\mathbb E[F(\bar x_T)-F(u)]
\le\frac{DG}{\sqrt T}.
\tag{95.12}
\]

This is an expected objective bound for the averaged iterate. It is not an almost-sure assertion that every run reaches this error, and it does not bound the last iterate without additional assumptions. If the horizon is unknown, a decreasing step schedule can avoid choosing \(\eta\) from \(T\), but its weighted telescope must be proved separately.

~~~text
projection inequality for each sample
                |
conditional expectation and convexity
                v
       one-round expected bound
                |
       sum over the horizon
                v
      telescope squared distance
                |
       Jensen for the average
                v
       expected objective gap
~~~

The order is useful in a formal proof: first prove the deterministic geometry, then condition on the current history, and only afterward sum across time.

## 3. What variance changes

The convex theorem uses a bound on the full second moment. Smooth objectives allow a different analysis that isolates the variance more directly. Suppose \(F\) is \(L\)-smooth, bounded below by \(F_{\inf}\), and the oracle obeys

\[
\mathbb E[g_t\mid\mathcal F_t]=\nabla F(x_t),
\qquad
\mathbb E[\|g_t-\nabla F(x_t)\|^2\mid\mathcal F_t]\le\sigma^2.
\tag{95.13}
\]

For the unconstrained update \(x_{t+1}=x_t-\eta g_t\), the descent lemma and (95.6) give

\[
\mathbb E[F(x_{t+1})\mid\mathcal F_t]
\le F(x_t)-\eta\left(1-\frac{L\eta}{2}\right)\|\nabla F(x_t)\|^2
+\frac{L\eta^2\sigma^2}{2}.
\tag{95.14}
\]

When \(0<\eta\le1/L\), the coefficient of the gradient norm is at least \(\eta/2\). Summing and using the lower bound on \(F\) gives

\[
\frac1T\sum_{t=1}^T\mathbb E\|\nabla F(x_t)\|^2
\le\frac{2(F(x_1)-F_{\inf})}{\eta T}+L\eta\sigma^2.
\tag{95.15}
\]

This is a stationarity bound. It applies even when \(F\) is nonconvex, but it does not by itself prove a small objective gap or identify a global minimizer. With a fixed step size, the first term decreases with the horizon while the second remains: stochastic noise creates a floor. Smaller steps reduce that floor but also slow progress. Variance-reduction methods attack the noise term directly; Chapter 96 will formalize that idea for finite sums.

### 3.1 Mini-batching

Average \(b\) conditionally independent unbiased samples:

\[
\hat g_t=\frac1b\sum_{j=1}^b g_{t,j}.
\]

The average is still conditionally unbiased. Independence makes its conditional variance at most \(\sigma^2/b\) when each sample has variance at most \(\sigma^2\). Thus the noise term in (95.15) is at most \(L\eta\sigma^2/b\). Each update costs \(b\) oracle calls, so this is a tradeoff between parallel work, variance, and the number of updates. The variance divides by \(b\); the full second moment does not generally do so because it includes the nonzero mean gradient.

## 4. Two worked models

### 4.1 Empirical risk with a sampled data point

Let \(f_i(w)\) be the loss on example \(i\), and let \(F(w)=\frac1n\sum_i f_i(w)\). Uniformly sampling \(i_t\) gives \(g_t=\nabla f_{i_t}(w_t)\). Conditional on the past, \(w_t\) is fixed and the sample index is uniform, so the gradient is unbiased for \(\nabla F(w_t)\). If the losses are convex and the sampled gradients have norm at most \(G\), (95.12) bounds the expected excess empirical risk of the averaged iterate.

If the data set is large, the cost difference from full gradient descent is substantial: one stochastic update uses one example instead of all \(n\). But increasing the number of updates also increases the number of examples processed. Compare algorithms by oracle calls or data passes, not just iteration count. At an empirical minimizer, gradients of individual examples need not vanish; equation (95.7) captures this residual noise.

### 4.2 A quadratic with additive noise

Consider \(F(x)=\frac12\|x-a\|^2\) and a noisy gradient \(g_t=x_t-a+\epsilon_t\), with
\[
\mathbb E[\epsilon_t\mid\mathcal F_t]=0,
\qquad
\mathbb E[\|\epsilon_t\|^2\mid\mathcal F_t]=\sigma^2.
\]
For the update \(x_{t+1}=x_t-\eta g_t\), write \(e_t=x_t-a\). Then

\[
e_{t+1}=(1-\eta)e_t-\eta\epsilon_t.
\]

The cross term vanishes conditionally, so

\[
\mathbb E[\|e_{t+1}\|^2\mid\mathcal F_t]
=(1-\eta)^2\|e_t\|^2+\eta^2\sigma^2.
\tag{95.16}
\]

For \(0<\eta<2\), the expected squared error approaches the noise level

\[
\frac{\eta^2\sigma^2}{1-(1-\eta)^2}
=\frac{\eta\sigma^2}{2-\eta}.
\tag{95.17}
\]

More precisely, after \(T-1\) updates,

\[
\mathbb E\|e_T\|^2
=(1-\eta)^{2(T-1)}\|e_1\|^2
+\frac{\eta\sigma^2}{2-\eta}
\left(1-(1-\eta)^{2(T-1)}\right).
\tag{95.18}
\]

With a nonzero constant step size, the iterate fluctuates rather than settling exactly at \(a\). Reducing \(\eta\) lowers the limiting error but makes the geometric factor \((1-\eta)^2\) closer to one. This exact example illustrates the general balance in (95.15).

## 5. Lean proof architecture

### 5.1 Separate the sample space from the deterministic update

Represent the random gradient as an integrable function from a probability space into the finite-dimensional decision space. Represent \(\mathcal F_t\) as the information available before the next sample. The iterate must be measurable with respect to that information; the stochastic gradient must be integrable; and the conditional mean and variance hypotheses are statements relative to that filtration.

Avoid defining the optimizer as a single random object if the proof only needs its expected behavior. Keep the update as a deterministic map of the current iterate and sampled gradient. Prove (95.9) for every gradient vector first. This lemma has no probability assumptions and can be reused by deterministic projected descent.

A small certificate can expose precisely the geometric fact needed by the probability layer:

~~~lean
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ProjectionRoundCert
    (C : Set E) (x xNext g : E) (η : ℝ) : Prop where
  next_mem : xNext ∈ C
  distance_bound : ∀ u, u ∈ C →
    ‖xNext - u‖ ^ 2 ≤ ‖x - η • g - u‖ ^ 2
~~~

The actual projection theorem constructs this certificate for \(xNext=P_C(x-\eta g)\). A stochastic proof can then instantiate the certificate at each outcome and take its conditional expectation. This keeps the projection API out of the oracle structure and makes the deterministic theorem available to other algorithms.

### 5.2 Package conditional oracle facts

An oracle interface should expose, for each time index, the following propositions:

- the iterate is measurable with respect to the past;
- the sampled gradient is integrable (and has an integrable squared norm);
- its conditional expectation is a subgradient of the objective at the current iterate;
- its conditional second moment is bounded by \(G^2\), or its conditional variance is bounded by \(\sigma^2\).

These are separate fields because they serve different proof steps. Measurability allows the current iterate to leave a conditional expectation. Unbiasedness supplies the subgradient inequality. The moment bound controls the quadratic update term. A variance bound cannot be silently substituted for a second-moment bound.

### 5.3 Use conditional expectation before full expectation

The key one-round proof is easiest when stated conditionally on \(\mathcal F_t\). Apply conditional expectation to the samplewise projection inequality, rewrite the inner product using the conditional mean, and apply convexity pointwise at \(x_t\). Then use the tower property to obtain a full-expectation inequality. This order makes the dependence on the random iterate explicit and avoids an invalid factorization of correlated random variables.

In a Lean development, first identify the exact conditional-expectation API for the pinned Mathlib version and prove a small lemma for pulling out an \(\mathcal F_t\)-measurable vector. The textbook theorem should depend on that lemma, not on an assumed independence statement stronger than the mathematics requires.

### 5.4 Keep the horizon argument finite

Index rounds by a finite type or a list of length \(T\). Sum (95.10), normalize using \(T>0\) and \(\eta>0\), and discard the nonnegative terminal distance. Define the average iterate from exactly the predictions \(x_1,\ldots,x_T\) appearing in the regret sum. A separate pathwise finite-Jensen lemma proves feasibility and compares its objective value to the average of the losses.

For (95.14), keep the descent lemma as a deterministic theorem about one update. The variance decomposition (95.6) and conditional unbiasedness are then applied in an expectation wrapper. This avoids mixing smooth calculus, probability, and finite telescoping in one large theorem.

## 6. Common failure modes

1. **Using unconditional unbiasedness.** The iterate depends on the past; condition on that past before replacing the sample gradient by the true one.
2. **Confusing variance and second moment.** A bounded variance does not bound a large mean gradient.
3. **Claiming a pathwise result from an expectation inequality.** (95.12) bounds expected error.
4. **Forgetting feasibility of the average.** Jensen applies on \(C\) because \(C\) is convex.
5. **Bounding the last iterate with an average-iterate theorem.** The proof controls \(\bar x_T\), not automatically \(x_T\).
6. **Assuming the gradient noise vanishes at the optimum.** Finite-sum component gradients can cancel without each being zero.
7. **Treating mini-batching as reducing the full second moment by \(b\).** It reduces the variance under conditional independence.
8. **Reading the smooth stationarity bound as a convexity theorem.** (95.15) bounds averaged squared gradient norms, not objective suboptimality.
9. **Ignoring integrability.** Conditional expectations and squared-norm identities need appropriate integrability hypotheses.
10. **Proving the algorithm and probability argument at once.** Isolate the deterministic projection certificate and conditional-oracle lemma first.

## 7. Exercises

1. Prove the projection inequality (95.9) from nonexpansiveness of \(P_C\).
2. Derive (95.10) using conditional unbiasedness and the subgradient inequality.
3. Sum (95.10), apply pathwise Jensen, and obtain (95.11).
4. Optimize the constant step size in (95.11) to prove (95.12).
5. For a uniform finite-sum oracle, derive the conditional variance formula (95.7).
6. Show that a variance bound alone does not imply the second-moment bound (95.5).
7. Derive the smooth descent inequality (95.14) and the stationarity bound (95.15).
8. Prove that the variance of a conditionally independent mini-batch average is \(\sigma^2/b\).
9. Solve the scalar recurrence in (95.16) and verify its limiting error (95.17).
10. Formalize the deterministic projection certificate for an arbitrary vector \(g_t\), without introducing probability.
11. Design an oracle structure with conditional mean and moment fields, then state the expected one-round theorem using that interface.
12. Give a finite-sum example where the objective gradient vanishes at its minimizer while component gradients have positive variance.

## 8. Chapter summary

Stochastic gradient descent replaces the exact gradient with a sample-based estimate. Conditional unbiasedness is essential because the current iterate depends on previous samples. A deterministic projection inequality, followed by conditional expectation and a finite telescoping sum, gives an expected \(O(T^{-1/2})\) objective bound for the averaged iterate under a bounded second moment.

For smooth objectives, a variance bound yields a stationarity estimate with a noise floor proportional to the step size. Mini-batching divides that variance by the batch size when samples are conditionally independent. A quadratic example shows exactly why constant-step stochastic methods fluctuate around an optimum.

In Lean, separate the deterministic update certificate, filtration and oracle hypotheses, conditional-expectation argument, and finite-horizon telescope. The result is a proof that states precisely what randomness buys and which conclusions remain only in expectation.

## Further reading

- Nemirovski, Juditsky, Lan, and Shapiro, [“Robust Stochastic Approximation Approach to Stochastic Programming”](https://epubs.siam.org/doi/10.1137/070704277), for stochastic approximation and expected convergence guarantees.
- Johnson and Zhang, [“Accelerating Stochastic Gradient Descent using Predictive Variance Reduction”](https://proceedings.neurips.cc/paper/2013/hash/ac1dd209cbcc5e5d1c6e28598e8cbbe8-Abstract.html), for the finite-sum control-variate method developed in the next chapter.
