# Chapter 105 — Finite-Sum Frank–Wolfe: Variance Reduction and Gap Estimation

> **Audience.** This chapter builds on the control variates of Chapter 96 and the stochastic oracle analysis of Chapter 104. It specializes those ideas to finite-sum Frank–Wolfe methods, where the estimator must support both a descent argument and a trustworthy stationarity diagnostic.

Frank–Wolfe is attractive when a feasible set is easy to optimize over linearly but difficult to project onto. In machine learning, the objective is often a finite average, and computing its full gradient may require touching every training example. A stochastic gradient lowers the per-step cost, but it can change the atom returned by the linear minimization oracle. Variance reduction addresses the first cost; analysis of the Frank–Wolfe gap addresses the second.

The key design principle is to keep three interfaces separate: a finite-sum gradient estimator, a linear oracle applied to that estimator, and a gap estimator or error bar used to judge progress. SVRG and SAGA provide familiar estimator states. Frank–Wolfe then consumes their error bounds through a diameter estimate. This chapter derives that composition, works through snapshot and gradient-table examples, and shows how to represent the proof obligations in Lean.

## Learning objectives

After this chapter, you should be able to:

- derive the SVRG and SAGA estimators for a finite-sum objective;
- prove unbiasedness conditional on the current algorithm state;
- turn component smoothness into a variance bound around an SVRG snapshot;
- combine a variance certificate with the noisy-oracle descent inequality;
- distinguish a sampled maximum gap from a specially designed stochastic gap estimator;
- formalize the estimator state and oracle certificate as separate Lean interfaces.

## 1. The finite-sum Frank–Wolfe problem

### 1.1 Objective, domain, and linear oracle

Let \(\mathcal K\) be a compact convex subset of a finite-dimensional Euclidean space, with diameter at most \(D\). Measure the diameter, smoothness, and gradient-estimator second moments in the Euclidean norm. In a more general normed setting, the deterministic oracle perturbation still uses a norm and its dual, but the variance estimate must be supplied for that geometry rather than inferred from centering alone. Consider the smooth finite-sum objective

\[
F(x)=\frac1n\sum_{i=1}^{n} f_i(x), \qquad x\in\mathcal K.
\tag{105.1}
\]

At a feasible point \(x_t\), the exact Frank–Wolfe atom is any solution of

\[
s_t^\star\in\arg\min_{s\in\mathcal K}\langle\nabla F(x_t),s\rangle.
\tag{105.2}
\]

The corresponding gap is

\[
G(x_t)=\max_{s\in\mathcal K}\langle\nabla F(x_t),x_t-s\rangle
=\langle\nabla F(x_t),x_t-s_t^\star\rangle.
\tag{105.3}
\]

For convex \(F\), this gap bounds the objective error from above:
\(F(x_t)-\min_{x\in\mathcal K}F\le G(x_t)\). For nonconvex \(F\), a small gap is a first-order stationarity certificate. Chapters 98 and 103 develop these deterministic interpretations.

The exact step is
\[
x_{t+1}=x_t+\gamma_t(s_t^\star-x_t), \qquad \gamma_t\in[0,1].
\tag{105.4}
\]
It remains feasible because it is a convex combination. Its expensive component is often not (105.2), but the full gradient in that equation. If evaluating one component gradient costs one unit, then one exact step costs \(n\) such evaluations, even when the linear oracle itself is cheap.

### 1.2 Replace the full gradient, preserve the certificate

Suppose an estimator \(v_t\) approximates \(\nabla F(x_t)\), and choose

\[
s_t\in\arg\min_{s\in\mathcal K}\langle v_t,s\rangle,
\qquad
x_{t+1}=x_t+\gamma_t(s_t-x_t).
\tag{105.5}
\]

Feasibility remains pathwise, but \(s_t\) need not equal \(s_t^\star\). Write
\(e_t=v_t-\nabla F(x_t)\). The diameter and dual norm imply

\[
\left|\langle e_t,x_t-s\rangle\right|
\le D\|e_t\|_*.
\tag{105.6}
\]

As in Chapter 104, comparing the noisy maximizer with the exact maximizer gives the true directional progress estimate

\[
\langle\nabla F(x_t),x_t-s_t\rangle
\ge G(x_t)-2D\|e_t\|_*.
\tag{105.7}
\]

The LMO nonlinearity is handled once, in this geometric lemma. The estimator-specific proof should not re-derive it. Instead, each stochastic-gradient method supplies a bound on \(\|e_t\|_*\) or its expectation.

~~~text
finite-sum component gradients
          |
          v
SVRG snapshot or SAGA table
          |
          v
  estimator v_t ---- error certificate ----+
          |                                  |
          v                                  |
   linear minimization oracle                |
          |                                  |
          v                                  |
       atom s_t                              |
          +----------- diameter bound -------+
                          |
                          v
                expected gap guarantee
~~~


## 2. Snapshot and table estimators

### 2.1 SVRG: compare at the same sampled component

Fix a snapshot \(\tilde x\), compute the full gradient \(\nabla F(\tilde x)\), and sample an index \(i\) uniformly from \(\{1,\ldots,n\}\). The SVRG estimator is

\[
v_i(x;\tilde x)
=\nabla f_i(x)-\nabla f_i(\tilde x)+\nabla F(\tilde x).
\tag{105.8}
\]

The correction adds back the average of the term subtracted on the sampled component. Conditional on the current point and snapshot,

\[
\mathbb E_i[v_i(x;\tilde x)]
=\nabla F(x)-\nabla F(\tilde x)+\nabla F(\tilde x)
=\nabla F(x).
\tag{105.9}
\]

The use of the *same* index in both component gradients is essential. If the two terms were sampled independently, their difference would still have the right mean, but the covariance cancellation that controls the variance would be lost.

Assume each component gradient is \(L\)-Lipschitz in the chosen norm. Centering cannot increase a second moment, so

\[
\begin{aligned}
\mathbb E_i\|v_i(x;\tilde x)-\nabla F(x)\|_*^2
&\le \mathbb E_i\|\nabla f_i(x)-\nabla f_i(\tilde x)\|_*^2\\
&\le L^2\|x-\tilde x\|^2.
\end{aligned}
\tag{105.10}
\]

For a minibatch of \(b\) independent samples averaged together, the conditional variance is at most \(L^2\|x-\tilde x\|^2/b\). This bound is deliberately local: it controls variance when the iterate stays near its snapshot. It does not by itself imply that the variance decreases over the run. The epoch length and the movement of \(x_t\) from \(\tilde x\) still need analysis.

In Euclidean space, a stronger bound can be obtained when the components are convex and smooth and an unconstrained minimizer is available. Chapter 96 proves the familiar objective-gap estimate
\[
\mathbb E_i\|v_i(x;\tilde x)\|^2
\le 4L\bigl(F(x)-F(x^\star)+F(\tilde x)-F(x^\star)\bigr).
\tag{105.11}
\]
The two gaps have distinct roles: the first measures current error, while the second measures the cost of a stale snapshot. The distance form (105.10) is often the cleaner interface for a Frank–Wolfe proof; the objective-gap form can be useful when the algorithm already tracks objective suboptimality.

### 2.2 SAGA: correct with a gradient table

SAGA stores one vector \(\alpha_i\) for each component and maintains their average
\(\bar\alpha=n^{-1}\sum_i\alpha_i\). It samples \(i\) uniformly and forms

\[
v_i(x;\alpha)
=\nabla f_i(x)-\alpha_i+\bar\alpha.
\tag{105.12}
\]

Conditioned on the table and the current point, the sample index is still uniform, hence

\[
\mathbb E_i[v_i(x;\alpha)]
=\nabla F(x)-\bar\alpha+\bar\alpha
=\nabla F(x).
\tag{105.13}
\]

After forming the estimator, replace the selected entry with the new component gradient:
\(\alpha_i\gets\nabla f_i(x)\). The order matters. The estimator uses the old table average; the state update occurs afterward. In a formal model, these are two transitions, not a single ambiguous mutation.

SAGA avoids recomputing a full snapshot gradient each epoch, but the table costs memory proportional to \(n\) times the gradient dimension. Its variance depends on how stale the entries are. This creates a different invariant from SVRG: the table average must agree with the stored entries, and the new table must differ from the old table only at the sampled index. Chapter 96 develops the optimization-specific variance estimates; here the important fact is that the unbiasedness proof is a short finite-sum identity.

### 2.3 Estimator costs are not oracle costs

A Frank–Wolfe iteration may use one component-gradient sample, one linear-oracle call, and a small update to an active representation. An SVRG epoch also pays for the full snapshot gradient. A SAGA step pays for maintaining its table. These costs should be reported separately.

A useful cost ledger has at least four columns:

| Method | Component-gradient work | Linear-oracle work | Extra state |
| --- | --- | --- | --- |
| Full-gradient FW | \(n\) per step | one per step | current iterate |
| SVRG-FW | \(n\) per snapshot plus two per sampled step | one per step | snapshot and full gradient |
| SAGA-FW | one per step, plus optional table initialization | one per step | \(n\)-entry gradient table |

The table hides problem-dependent details: a structured LMO may have its own complexity, and some generalized linear models can share computations across examples. The ledger prevents a proof from claiming a per-iteration improvement while silently omitting epoch or memory costs.


## 3. Feed variance into a Frank–Wolfe rate

### 3.1 A reusable expected-gap theorem

Assume \(F\) is \(L_F\)-smooth on \(\mathcal K\), with diameter \(D\), and that each iterate and estimator state is determined by the past before the next independent sample is drawn. Suppose the estimator is conditionally unbiased and define

\[
\rho_t=\mathbb E\|v_t-\nabla F(x_t)\|_*.
\tag{105.14}
\]

Smoothness and (105.7) yield

\[
\mathbb E[F(x_{t+1})]
\le \mathbb E[F(x_t)]
-\gamma_t\mathbb E[G(x_t)]
+2\gamma_tD\rho_t
+\frac{L_F\gamma_t^2D^2}{2}.
\tag{105.15}
\]

This is a direct specialization of Chapter 104. It consumes the *first moment* of the estimator error, even when the estimator analysis naturally gives a second moment. In that case, Jensen and Cauchy–Schwarz give
\(\rho_t\le\sqrt{\mathbb E\|v_t-\nabla F(x_t)\|_*^2}\).

For a fixed step size \(\gamma\in(0,1]\), let
\(h_0=F(x_0)-F_{\min}\), where \(F_{\min}\) is a lower bound on \(F\) over \(\mathcal K\). Summing (105.15) for \(T\) steps and rearranging gives

\[
\frac1T\sum_{t=0}^{T-1}\mathbb E[G(x_t)]
\le
\frac{h_0}{\gamma T}
+\frac{2D}{T}\sum_{t=0}^{T-1}\rho_t
+\frac{L_F\gamma D^2}{2}.
\tag{105.16}
\]

No convexity of \(F\) is required for this stationarity result. A uniformly sampled independent output index \(\tau\) satisfies the same right-hand side as an upper bound on \(\mathbb E[G(x_\tau)]\).

The theorem is an interface, not a complete SVRG-FW convergence rate. To finish a rate proof, one must bound the average snapshot distances in (105.10), or establish a stronger objective-gap variance estimate, under the actual epoch schedule and FW update. This is where Frank–Wolfe geometry and variance reduction interact. Importing a gradient-descent SVRG epoch contraction without rechecking its update assumptions is not valid.

### 3.2 A variance budget for minibatched SVRG

Suppose the estimator averages \(b\) independent SVRG samples at state \(x_t\) with snapshot \(\tilde x_t\). From (105.10),

\[
\rho_t
\le \frac{L}{\sqrt b}
\left(\mathbb E\|x_t-\tilde x_t\|^2\right)^{1/2}.
\tag{105.17}
\]

Substitution into (105.16) shows exactly what the variance-reduced analysis still owes: an upper bound on the mean squared distance from the snapshot. For example, if an epoch proof establishes
\(\mathbb E\|x_t-\tilde x_t\|^2\le R^2\) at each inner step, then its contribution to the average gap is at most \(2DLR/\sqrt b\). If the bound grows with the inner-step index, sum the individual square roots or use a sharper average estimate; do not replace them by a constant without justification.

This decomposition is valuable even before one proves a polished asymptotic rate. It lets the estimator lemma and the algorithm-specific epoch lemma be developed independently. A changed sampling scheme, a different step schedule, or a new update rule may alter the distance estimate while leaving the LMO perturbation and descent theorem untouched.

### 3.3 Biased estimators and recursive errors

Not every efficient estimator is conditionally unbiased. Momentum and recursive estimators may instead satisfy an error recursion. Let
\(b_t=\|\mathbb E[v_t-\nabla F(x_t)\mid\mathcal F_t]\|_*\) be its conditional bias and let
\(q_t=\mathbb E[\|v_t-\nabla F(x_t)\|_*^2\mid\mathcal F_t]\).
The conditional direction argument contains the bias explicitly:

\[
\mathbb E[\langle\nabla F(x_t),x_t-s_t\rangle\mid\mathcal F_t]
\ge G(x_t)-2D\sqrt{q_t}.
\tag{105.18}
\]

Here the bound uses the conditional second moment of the full error, so bias is already included. If the method supplies only a centered variance bound, then add a separate \(2Db_t\) contribution. The theorem’s hypotheses must match the exact estimator certificate; “small variance” alone does not imply “small total error.”

An error recursion often has the schematic form
\[
\mathbb E\|e_t\|_*^2
\le a_t\mathbb E\|e_{t-1}\|_*^2
+b_t\mathbb E\|x_t-x_{t-1}\|^2+c_t.
\tag{105.19}
\]
A complete proof may combine this with objective decrease in a Lyapunov function. Lean should not bury the recursion inside the final theorem: first prove the estimator-state invariant, then show how its accumulated error enters (105.16).


## 4. Gap estimation and stopping

### 4.1 The sampled maximum is biased

A tempting diagnostic is to replace the true gradient in the gap by a sampled gradient:
\[
\widehat G(v,x)=\max_{s\in\mathcal K}\langle v,x-s\rangle.
\tag{105.20}
\]
Even if \(\mathbb E[v]=\nabla F(x)\), this quantity is generally not an unbiased estimate of \(G(x)\). For fixed \(x\), the map
\(v\mapsto\max_{s\in\mathcal K}\langle v,x-s\rangle\) is convex, so Jensen’s inequality gives

\[
\mathbb E[\widehat G(v,x)]\ge G(x).
\tag{105.21}
\]

The inequality is in the safe direction for an upper bound only in a very limited sense: an upward-biased random number is not a calibrated confidence bound. It may fluctuate substantially, and a single sample does not quantify uncertainty. Conversely, using the gap from a noisy selected atom with the true gradient is not directly observable unless the true gradient is computed.

### 4.2 Worked example: zero true gap, positive sampled gap

Let \(\mathcal K\) be the simplex with vertices \(e_1,e_2\), and let \(x=(1/2,1/2)\). Suppose a random gradient estimate equals \(e_1\) or \(e_2\), each with probability \(1/2\). Its mean is \((1/2,1/2)\), whose linear objective is constant on the simplex; therefore the true FW gap is zero.

For the sample \(v=e_1\), the noisy LMO chooses \(e_1\) and the sampled gap is
\(\langle e_1,x-e_1\rangle=1/2\). For the other sample it is again \(1/2\). Thus

\[
G(x)=0,\qquad \mathbb E[\widehat G(v,x)]=\frac12.
\tag{105.22}
\]

This is exactly the convexity bias in (105.21), not a contradiction. It also shows why a positive noisy gap need not mean that the true iterate is nonstationary.

### 4.3 Structured gap estimators

Specialized finite-sum algorithms can estimate or certify the FW gap by exploiting additional prediction structure. For a generalized linear objective such as
\(F(x)=n^{-1}\sum_i \ell_i(\langle a_i,x\rangle)\), the gradient is a sum of feature vectors weighted by prediction residuals. If the model and feasible set permit a suitable sampled summary, an algorithm may obtain a useful gap estimator without evaluating every component at every iteration.

That construction is problem-dependent. It is not the generic sampled maximum in (105.20), and its validity comes from its own identity or concentration analysis. Negiar and coauthors give a stochastic Frank–Wolfe method for constrained finite sums with generalized linear prediction structure and describe a stochastic FW-gap estimator as a stopping criterion. When formalizing such a method, state the structural assumptions and the guarantee of the estimator explicitly. Do not transfer its stopping rule to an arbitrary finite sum.

A good stopping interface returns more than a scalar. It records the estimator’s target, its bias or confidence guarantee, the sampling assumptions, and the event or expectation under which the claim holds. Deterministic certificates, expected stationarity bounds, and high-probability stopping guarantees are different outputs.


## 5. Worked examples with estimator state

### 5.1 SVRG can remove component disagreement

Consider two scalar component functions
\(f_1(x)=\tfrac12(x-1)^2\) and \(f_2(x)=\tfrac12(x+1)^2\). Their average is
\(F(x)=\tfrac12x^2+\tfrac12\), so \(F'(x)=x\). Take snapshot \(\tilde x=0\) and current point \(x=1\). Then \(F'(\tilde x)=0\). The component derivatives are

\[
f_1'(1)=0,\quad f_1'(0)=-1,\qquad
f_2'(1)=2,\quad f_2'(0)=1.
\]

If the sampled index is 1, (105.8) gives \(0-(-1)+0=1\). If it is 2, it gives \(2-1+0=1\). The estimate equals the full gradient \(F'(1)=1\) for either sample, even though the individual current gradients are 0 and 2. The shared-index difference has canceled all sampling variance in this example.

If instead the snapshot were \(\tilde x=1\), the estimator would also equal the exact gradient at \(x=1\) for either index, because the component differences vanish and the full snapshot gradient is already exact. The first calculation is more instructive: exactness can arise from cancellation before the snapshot reaches the current point.

Here is the calculation as two scalar component-gradient functions. Each theorem fixes one shared sample index and checks that its SVRG estimate equals the full gradient at the current point.

```lean
def componentGradientOne105 (x : ℝ) : ℝ := x - 1
def componentGradientTwo105 (x : ℝ) : ℝ := x + 1

noncomputable def fullGradient105 (x : ℝ) : ℝ :=
  (componentGradientOne105 x + componentGradientTwo105 x) / 2

noncomputable def svrgOne105 (x snapshot : ℝ) : ℝ :=
  componentGradientOne105 x - componentGradientOne105 snapshot + fullGradient105 snapshot

noncomputable def svrgTwo105 (x snapshot : ℝ) : ℝ :=
  componentGradientTwo105 x - componentGradientTwo105 snapshot + fullGradient105 snapshot

theorem full_gradient_at_snapshot_is_zero : fullGradient105 0 = 0 := by
  norm_num [fullGradient105, componentGradientOne105, componentGradientTwo105]

theorem full_gradient_at_current_point_is_one : fullGradient105 1 = 1 := by
  norm_num [fullGradient105, componentGradientOne105, componentGradientTwo105]

theorem svrg_sample_one_is_exact : svrgOne105 1 0 = fullGradient105 1 := by
  norm_num [svrgOne105, fullGradient105, componentGradientOne105,
    componentGradientTwo105]

theorem svrg_sample_two_is_exact : svrgTwo105 1 0 = fullGradient105 1 := by
  norm_num [svrgTwo105, fullGradient105, componentGradientOne105,
    componentGradientTwo105]
```

### 5.2 SAGA unbiasedness depends on the old table

Let \(f_1(x)=\tfrac12x^2\) and \(f_2(x)=x^2\), so their derivatives are \(x\) and \(2x\). At current point \(x=2\), let the stored table be \(\alpha_1=1\) and \(\alpha_2=0\); hence \(\bar\alpha=1/2\). The two possible SAGA estimates are

\[
v_1=2-1+\tfrac12=\tfrac32,\qquad
v_2=4-0+\tfrac12=\tfrac92.
\]

Their average is \(3\), the full derivative \(F'(2)=(2+4)/2=3\). If index 1 is sampled, only after computing \(v_1\) do we replace \(\alpha_1\) by 2. The new table mean is 1, not \(1/2\). Reusing the updated mean in the same estimator would produce a different random vector and spoil this proof.

These examples illustrate a general formalization pattern: first prove that the estimator’s mean is the full gradient for a fixed algorithm state; then model the state transition and prove its invariant. Mixing those two steps makes index-update order difficult to audit.


## 6. Lean proof architecture

### 6.1 Separate finite averaging from analytic assumptions

Represent the component family by an index type with a finite uniform distribution, and define the full gradient as its average. Prove the SVRG unbiasedness identity using only finite-sum algebra. Do not include convexity, smoothness, compactness, or a linear oracle in that lemma. The identity should remain reusable if the algorithm changes.

The following is an interface sketch, not a complete Mathlib declaration. Its purpose is to show the dependency boundary:

~~~lean
structure FiniteSumEstimator (State : Type*) (E : Type*) where
  sample : State → Fin n → E
  mean_eq_fullGradient : ...
  error_certificate : ...

structure LinearOracleCertificate (E : Type*) (K : Type*) where
  atom : E → K
  optimal_for_input : ...

structure FWStepCertificate (K : Type*) where
  feasible_update : ...
  true_progress_bound : ...
~~~

The estimator certificate concerns the distribution of component samples and the state on which they are conditioned. The oracle certificate concerns a linear objective and its selected atom. The step certificate concerns convex combinations and geometry. The final convergence theorem composes these records; it should not need to inspect how an estimator obtains its variance bound.

### 6.2 Model SAGA updates without mutation

For SAGA, define the algorithm state as a current point paired with a finite function from component indices to gradient values. Sampling an index produces an estimator from the old state and a new state with exactly one table entry replaced. Prove a table-average update lemma by splitting the finite sum into the selected index and all remaining indices. The average change is then one vector difference divided by \(n\).

A pure state transition has practical advantages in Lean: it makes the order of reads and writes explicit, permits induction over iterations, and keeps the transition deterministic once the sampled index is supplied. Randomness can be introduced by averaging over the index afterward. This mirrors the paper proof and avoids mutable-array reasoning unless runtime performance is actually needed.

### 6.3 Telescope through weighted certificates

For variable step sizes, do not divide by \(T\) prematurely. Sum the one-step inequalities as

\[
\sum_{t<T}\gamma_t\,\mathbb E[G(x_t)]
\le h_0+2D\sum_{t<T}\gamma_t\rho_t
+\frac{L_FD^2}{2}\sum_{t<T}\gamma_t^2.
\tag{105.23}
\]

This weighted statement is the stable theorem. A particular output distribution can be layered on top by sampling \(\tau\) with probability proportional to \(\gamma_t\), provided the weights are nonnegative and sum to a positive value. The resulting expectation equals the normalized weighted gap sum. Keeping this as a second lemma makes the telescoping algebra independent of the output policy.

For Lean, finite telescoping should be stated over `Finset.range T`, with a separate lemma for the sequence identity. Analytic integrability and conditional expectation belong in the probability layer; the finite algebra should not carry measure-theoretic hypotheses it does not use. These boundaries echo the proof architecture in Chapters 35–36 and 104.


## 7. Common failure modes

1. **Using two independent component indices in SVRG.** Unbiasedness may survive, but the same-sample cancellation behind (105.10) does not.
2. **Assuming snapshot variance automatically shrinks.** It shrinks with distance to the snapshot; the epoch proof must control that distance.
3. **Treating an SVRG gradient-descent rate as an SVRG-FW rate.** The update geometry and available inequalities differ.
4. **Forgetting the batch factor.** Averaging \(b\) independent estimates divides variance by \(b\), and standard deviation by \(\sqrt b\).
5. **Conflating estimator variance and total error.** Bias must be included in the error certificate.
6. **Updating the SAGA table too early.** The estimator uses the old table and its old mean.
7. **Ignoring snapshot setup cost.** The full gradient at an SVRG snapshot costs \(n\) component evaluations.
8. **Treating the noisy maximum as unbiased.** The maximum is convex in its gradient argument and is generally upward-biased.
9. **Calling an expected gap a stopping certificate.** Expected bounds do not supply deterministic or high-probability guarantees.
10. **Combining gradient and LMO costs.** They are distinct operations and should have separate complexity counts.
11. **Overloading one Lean theorem.** Estimator identities, variance bounds, oracle perturbation, and telescoping have different hypotheses and should be separate lemmas.
12. **Hiding sampling assumptions.** Uniformity, independence, and conditioning on the past are part of the theorem, not implementation commentary.

## 8. Exercises

1. Prove the SVRG unbiasedness identity (105.9) by expanding the finite average.
2. Show that centering a random vector cannot increase its second moment, and use it to derive (105.10).
3. Derive the \(1/b\) variance factor for an average of \(b\) conditionally independent SVRG samples.
4. For a general estimator with error \(e_t\), prove the diameter perturbation bound (105.7).
5. Sum the one-step inequality to establish (105.16), stating where the lower bound \(F_{\min}\) is used.
6. Repeat the SAGA calculation in (105.13) for a table with three components and a nonzero table mean.
7. In the simplex example, calculate the gap for each random gradient and verify the strict Jensen bias.
8. Give an example where the sampled gap is unbiased. State what property of the feasible set or random gradient makes equality hold.
9. Propose a finite-state representation of the SAGA table and state an invariant for its average.
10. Explain which hypotheses would be needed to upgrade an expected gap estimate to a high-probability stopping rule.
11. Compare total gradient evaluations for \(S\) SVRG epochs of length \(m\) and \(T\) SAGA iterations, including setup and table memory.
12. State a Lean lemma for the weighted telescope (105.23) that does not mention probability measures.

## 9. Chapter summary

Finite-sum Frank–Wolfe methods reduce gradient cost by replacing the full gradient with an estimator, while retaining the same convex-combination feasibility mechanism. SVRG uses a shared-index difference and a snapshot gradient; SAGA uses a component-gradient table. Each estimator has an algebraic unbiasedness proof and a separate variance proof.

Frank–Wolfe converts estimator error into direction error through the feasible-set diameter. The resulting expected-gap theorem is method-independent, while a concrete variance-reduced rate still requires an epoch or table analysis that controls estimator error along the actual FW iterates. A sampled maximum gap is generally upward-biased and should not be mistaken for a calibrated stopping rule. In Lean, separate finite averaging, estimator state, variance, oracle perturbation, and weighted telescoping into small interfaces.

## Further reading

- Hazan and Luo, [“Variance-Reduced and Projection-Free Stochastic Optimization”](https://proceedings.mlr.press/v48/hazana16.html), for variance-reduced stochastic Frank–Wolfe variants.
- Negiar et al., [“Stochastic Frank-Wolfe for Constrained Finite-Sum Minimization”](https://proceedings.mlr.press/v119/negiar20a.html), for structured finite-sum objectives and stochastic gap estimation.
- Chapters 96 and 104, for general SVRG/SAGA analysis and the noisy Frank–Wolfe oracle perturbation argument.

