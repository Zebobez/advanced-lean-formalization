# Chapter 106 — Structured Gap Estimation for Generalized Linear Frank–Wolfe

> **Audience.** This chapter develops the structured finite-sum method previewed in Chapter 105. It assumes familiarity with Frank–Wolfe gaps, finite-sum objectives, and conditional expectation. The focus is a cached derivative table whose linear image supplies both the LMO direction and a stochastic gap estimate.

Chapter 105 showed that replacing a full gradient by a sample and then maximizing over the feasible set generally creates a biased gap value. Structure can make a more useful diagnostic possible. For generalized linear objectives, the full gradient is a linear image of one scalar derivative per data point. Refreshing one derivative at a time and maintaining their aggregate gives a low-cost oracle direction and a gap estimate whose error can be bounded by a data-dependent diameter.

The construction is subtle in two ways. First, its derivative table is not a conditionally unbiased gradient estimator at each iteration: most coordinates are stale. The proof instead tracks a recursive error norm. Second, the apparent gap estimate is not automatically a deterministic certificate. Its reliability comes from a bound on that table error, and the practical stopping rule remains heuristic when the bound is unavailable or too loose.

## Learning objectives

After this chapter, you should be able to:

- rewrite a generalized linear finite sum as a separable loss composed with a data matrix;
- derive the one-coordinate update for a cached derivative table and its aggregate gradient;
- prove an estimator-error recurrence from uniform coordinate refresh and iterate movement;
- derive the extra error term in the Frank–Wolfe descent recurrence;
- bound the gap-estimation error using an \(\ell_1\)-\(\ell_\infty\) pairing;
- distinguish an expected-error proxy from a directly certified stopping rule;
- structure the state and invariants for a Lean formalization.

## 1. Linear prediction exposes coordinate structure

### 1.1 From examples to a separable map

Let \(X\in\mathbb R^{n\times d}\) have rows \(a_i^\top\), let \(\mathcal C\subseteq\mathbb R^d\) be compact and convex, and let each scalar loss \(\phi_i:\mathbb R\to\mathbb R\) be differentiable. The objective is

\[
F(w)=\frac1n\sum_{i=1}^n \phi_i(a_i^\top w),\qquad w\in\mathcal C.
\tag{106.1}
\]

Define the separable function
\[
\psi(z)=\frac1n\sum_{i=1}^n\phi_i(z_i),\qquad z\in\mathbb R^n.
\tag{106.2}
\]
Then \(F(w)=\psi(Xw)\), and the chain rule gives
\[
\nabla F(w)=X^\top\nabla\psi(Xw),\qquad
[\nabla\psi(Xw)]_i=\frac1n\phi_i'(a_i^\top w).
\tag{106.3}
\]

The dataset enters the parameter-space gradient only through the linear map \(X^\top\). If the coordinates of \(\nabla\psi(Xw)\) are stored, then refreshing one example changes the full-gradient proxy by a rank-one term. This is the computational structure that the algorithm exploits.

Assume each \(\phi_i'\) is \(L\)-Lipschitz. In Euclidean norm, \(\nabla\psi\) is \(L/n\)-Lipschitz:
\[
\|\nabla\psi(z)-\nabla\psi(z')\|_2
\le \frac{L}{n}\|z-z'\|_2.
\tag{106.4}
\]
The factor \(1/n\) comes from the normalization in (106.2); losing it changes the smoothness term in every rate.

### 1.2 The exact linear minimization oracle

For an exact gradient, Frank–Wolfe solves
\[
s^\star(w)\in\arg\min_{s\in\mathcal C}
\langle X^\top\nabla\psi(Xw),s\rangle
\tag{106.5}
\]
and moves toward \(s^\star(w)\). Equivalently, by the transpose identity,
\[
\langle X^\top q,s\rangle=\langle q,Xs\rangle.
\tag{106.6}
\]
This means the LMO consumes the aggregate \(X^\top q\); it does not need the individual losses once that aggregate is available.

The exact gradient still costs \(n\) scalar derivative evaluations. The stochastic method keeps a cached vector \(\alpha\in\mathbb R^n\), intended to approximate \(\nabla\psi(Xw)\), and a parameter-space vector
\[
r=X^\top\alpha.
\tag{106.7}
\]
The LMO uses \(r\). Unlike an unbiased minibatch estimate, \(\alpha\) retains stale values for examples that have not yet been sampled. Its error must be analyzed as state.


## 2. One-coordinate stochastic Frank–Wolfe

### 2.1 Refresh one contribution

At the beginning of iteration \(t\), the state is
\((w_{t-1},\alpha_{t-1},r_{t-1})\), with
\(r_{t-1}=X^\top\alpha_{t-1}\). Sample \(i_t\) uniformly from
\(\{1,\ldots,n\}\). Replace only the selected coordinate by its current derivative contribution:
\[
\alpha_t^{(i_t)}
=\frac1n\phi_{i_t}'(a_{i_t}^\top w_{t-1}),\qquad
\alpha_t^{(j)}=\alpha_{t-1}^{(j)}\quad(j\ne i_t).
\tag{106.8}
\]

Update the aggregate without recomputing the whole matrix product:
\[
r_t=r_{t-1}
+\bigl(\alpha_t^{(i_t)}-\alpha_{t-1}^{(i_t)}\bigr)a_{i_t}.
\tag{106.9}
\]
Then choose
\[
s_t\in\arg\min_{s\in\mathcal C}\langle r_t,s\rangle,
\qquad
w_t=(1-\gamma_t)w_{t-1}+\gamma_t s_t.
\tag{106.10}
\]
The standard schedule in the smooth convex analysis is
\(\gamma_t=2/(t+2)\). Since \(w_{t-1},s_t\in\mathcal C\) and
\(\gamma_t\in[0,1]\), feasibility is pathwise.

The sequence of operations matters. The selected derivative in (106.8) is evaluated at the old iterate \(w_{t-1}\); the LMO then uses the refreshed aggregate, and only afterward does the iterate move. A proof that evaluates the new derivative at \(w_t\) is analyzing a different algorithm.

### 2.2 The aggregate invariant

The key state invariant is
\[
r_t=X^\top\alpha_t.
\tag{106.11}
\]
If it holds at \(t-1\), then
\[
\begin{aligned}
X^\top\alpha_t
&=X^\top\alpha_{t-1}
+\bigl(\alpha_t^{(i_t)}-\alpha_{t-1}^{(i_t)}\bigr)X^\top e_{i_t}\\
&=r_{t-1}
+\bigl(\alpha_t^{(i_t)}-\alpha_{t-1}^{(i_t)}\bigr)a_{i_t}
=r_t.
\end{aligned}
\tag{106.12}
\]
Thus the incremental update is exactly the matrix product of the changed table, not an approximation to that matrix product. Approximation enters only because the unrefreshed table entries are stale relative to the current iterate.

The state uses \(n\) scalars for \(\alpha\) and \(d\) entries for \(r\). Each iteration evaluates one prediction and one scalar derivative, applies one feature-vector update, and makes one LMO call. For a dense example row the feature update costs \(O(d)\); for sparse data it can scale with the row’s nonzero entries. The method avoids an \(O(nd)\) full-gradient calculation per iteration, but it does not remove the need to access the sampled example or pay for the LMO.


## 3. A recursive error certificate

### 3.1 Measure stale-table error in the example coordinates

Let
\[
H_t=\|\alpha_t-\nabla\psi(Xw_{t-1})\|_1.
\tag{106.13}
\]
This norm is chosen to match the coordinate-wise table: each coordinate corresponds to one example. Let
\[
D_1=\max_{u,v\in\mathcal C}\|X(u-v)\|_1,\qquad
D_\infty=\max_{u,v\in\mathcal C}\|X(u-v)\|_\infty.
\tag{106.14}
\]
These are diameters after mapping feasible parameter differences into prediction space. They need not scale like the parameter-space diameter or like \(n\); the data and domain jointly determine them.

At iteration \(t\), the refreshed coordinate matches the gradient contribution at \(w_{t-1}\). Every unrefreshed coordinate has two sources of error: it may already have been stale at \(w_{t-2}\), and its true target changes as the iterate moves from \(w_{t-2}\) to \(w_{t-1}\). Uniform sampling refreshes each coordinate with probability \(1/n\). The expected stale portion is therefore multiplied by \(1-1/n\).

For each coordinate, scalar smoothness gives
\[
\left|
[\nabla\psi(Xw_{t-1})]_j-[\nabla\psi(Xw_{t-2})]_j
\right|
\le \frac{L}{n}|a_j^\top(w_{t-1}-w_{t-2})|.
\tag{106.15}
\]
Summing over coordinates and using
\(w_{t-1}-w_{t-2}=\gamma_{t-1}(s_{t-1}-w_{t-2})\) yields the conditional recurrence
\[
\mathbb E_t[H_t]
\le
\left(1-\frac1n\right)
\left(H_{t-1}+\frac{L\gamma_{t-1}D_1}{n}\right).
\tag{106.16}
\]
Here \(\mathbb E_t\) averages over the newly sampled index, with the history through iteration \(t-1\) fixed. The recurrence needs no conditional-unbiasedness claim for the full vector \(\alpha_t\). It directly controls the stale-coordinate error.

With \(\gamma_t=2/(t+2)\), repeatedly applying (106.16) gives a vanishing expected error of order \(1/t\), together with a geometrically decaying initialization term (and a smaller transient from the early step sizes). The contraction factor \(1-1/n\) reflects how long a coordinate may wait to be refreshed. A useful theorem statement keeps both the initialization \(H_0\) and the movement scale \(LD_1/n\) visible instead of hiding them in asymptotic notation.

### 3.2 Worked example: refresh, aggregate, and move

Take two examples in one dimension:
\[
a_1=1,\qquad a_2=2,\qquad
\phi_1(z)=\tfrac12(z-1)^2,\qquad
\phi_2(z)=\tfrac12(z+1)^2,
\tag{106.17}
\]
with feasible interval \(\mathcal C=[-1,1]\). Initialize \(w_0=0\), \(\alpha_0=(0,0)\), and \(r_0=0\). If the first sampled index is 1, then
\[
\alpha_1^{(1)}=\tfrac12\phi_1'(0)=-\tfrac12,\qquad
\alpha_1^{(2)}=0,\qquad r_1=-\tfrac12.
\]
The invariant \(r_1=X^\top\alpha_1\) holds. The LMO minimizes
\(-\tfrac12s\) over \([-1,1]\), so \(s_1=1\). With
\(\gamma_1=2/3\), the next iterate is \(w_1=2/3\).

Suppose the next sampled index is 2. Its refreshed coordinate is
\[
\alpha_2^{(2)}
=\tfrac12\phi_2'(2w_1)
=\tfrac12(4/3+1)=7/6,
\]
while \(\alpha_2^{(1)}=-1/2\) remains stale. Thus
\[
r_2=-\tfrac12+2\cdot\tfrac76=\tfrac{11}{6}.
\]
The true prediction-gradient table at \(w_1\) is
\(\nabla\psi(Xw_1)=(-1/6,7/6)\), so \(H_2=1/3\). Its parameter-space gradient is \(X^\top\nabla\psi(Xw_1)=13/6\); the cached aggregate \(11/6\) differs by \(1/3\), exactly the contribution of the stale first row.

Here \(D_\infty=4\), since the largest feature displacement over the interval is \(2\cdot 2=4\). The gap comparison below gives
\(|G(w_1)-\widehat G_2|\le4/3\). In fact both gradients choose the left endpoint as their LMO atom, and their observed gap difference is \(5/9\). The estimate is not exact, but its discrepancy is governed by the stale-table state rather than by the number of examples alone.

The Lean calculation below represents the two cached derivatives as a pair and computes the aggregate \(X^\top\alpha\) from the feature values. It checks both incremental aggregate updates, the table error, and the resulting gap discrepancy bound.

```lean
def featureOne106 : ℚ := 1
def featureTwo106 : ℚ := 2

def componentOneDerivative106 (z : ℚ) : ℚ := z - 1
def componentTwoDerivative106 (z : ℚ) : ℚ := z + 1

def initialPoint106 : ℚ := 0
def pointAfterFirstStep106 : ℚ := 2 / 3

def initialTable106 : ℚ × ℚ := (0, 0)

def tableAfterFirstRefresh106 : ℚ × ℚ :=
  (componentOneDerivative106 (featureOne106 * initialPoint106) / 2,
    initialTable106.2)

def tableAfterSecondRefresh106 : ℚ × ℚ :=
  (tableAfterFirstRefresh106.1,
    componentTwoDerivative106 (featureTwo106 * pointAfterFirstStep106) / 2)

def aggregate106 (table : ℚ × ℚ) : ℚ :=
  featureOne106 * table.1 + featureTwo106 * table.2

def aggregateAfterFirstRefresh106 : ℚ :=
  aggregate106 initialTable106 +
    (tableAfterFirstRefresh106.1 - initialTable106.1) * featureOne106

def aggregateAfterSecondRefresh106 : ℚ :=
  aggregateAfterFirstRefresh106 +
    (tableAfterSecondRefresh106.2 - tableAfterFirstRefresh106.2) * featureTwo106

theorem aggregate_invariant_after_first_refresh :
    aggregate106 tableAfterFirstRefresh106 = aggregateAfterFirstRefresh106 := by
  norm_num [aggregate106, aggregateAfterFirstRefresh106,
    tableAfterFirstRefresh106, initialTable106, componentOneDerivative106,
    featureOne106, featureTwo106, initialPoint106]

theorem aggregate_invariant_after_second_refresh :
    aggregate106 tableAfterSecondRefresh106 = aggregateAfterSecondRefresh106 := by
  norm_num [aggregate106, aggregateAfterSecondRefresh106,
    aggregateAfterFirstRefresh106, tableAfterSecondRefresh106,
    tableAfterFirstRefresh106, initialTable106, componentOneDerivative106,
    componentTwoDerivative106, featureOne106, featureTwo106,
    initialPoint106, pointAfterFirstStep106]

def trueTableAtPoint106 : ℚ × ℚ :=
  (componentOneDerivative106 (featureOne106 * pointAfterFirstStep106) / 2,
    componentTwoDerivative106 (featureTwo106 * pointAfterFirstStep106) / 2)

def tableError106 : ℚ :=
  |tableAfterSecondRefresh106.1 - trueTableAtPoint106.1| +
    |tableAfterSecondRefresh106.2 - trueTableAtPoint106.2|

theorem stale_table_error_is_one_third : tableError106 = 1 / 3 := by
  norm_num [tableError106, tableAfterSecondRefresh106, trueTableAtPoint106,
    tableAfterFirstRefresh106, initialTable106, componentOneDerivative106,
    componentTwoDerivative106, featureOne106, featureTwo106,
    initialPoint106, pointAfterFirstStep106]

def gradientGap106 (gradient : ℚ) : ℚ :=
  gradient * (pointAfterFirstStep106 + 1)

def cachedGradient106 : ℚ := aggregate106 tableAfterSecondRefresh106
def trueGradient106 : ℚ := aggregate106 trueTableAtPoint106

theorem cached_aggregate_is_eleven_sixths : cachedGradient106 = 11 / 6 := by
  norm_num [cachedGradient106, aggregate106, tableAfterSecondRefresh106,
    tableAfterFirstRefresh106, initialTable106, componentOneDerivative106,
    componentTwoDerivative106, featureOne106, featureTwo106,
    initialPoint106, pointAfterFirstStep106]

theorem true_aggregate_is_thirteen_sixths : trueGradient106 = 13 / 6 := by
  norm_num [trueGradient106, aggregate106, trueTableAtPoint106,
    componentOneDerivative106, componentTwoDerivative106,
    featureOne106, featureTwo106, pointAfterFirstStep106]

theorem observed_gap_difference_is_five_ninths :
    |gradientGap106 trueGradient106 - gradientGap106 cachedGradient106| = 5 / 9 := by
  norm_num [gradientGap106, trueGradient106, cachedGradient106,
    aggregate106, trueTableAtPoint106, tableAfterSecondRefresh106,
    tableAfterFirstRefresh106, initialTable106, componentOneDerivative106,
    componentTwoDerivative106, featureOne106, featureTwo106,
    initialPoint106, pointAfterFirstStep106]

theorem gap_error_is_bounded_by_data_diameter_times_table_error :
    |gradientGap106 trueGradient106 - gradientGap106 cachedGradient106| ≤
      4 * tableError106 := by
  norm_num [gradientGap106, trueGradient106, cachedGradient106,
    aggregate106, tableError106, trueTableAtPoint106,
    tableAfterSecondRefresh106, tableAfterFirstRefresh106,
    initialTable106, componentOneDerivative106, componentTwoDerivative106,
    featureOne106, featureTwo106, initialPoint106, pointAfterFirstStep106]
```


## 4. Descent and the data-dependent rate

### 4.1 Curvature plus estimator error

Define
\[
D_2=\max_{u,v\in\mathcal C}\|X(u-v)\|_2,\qquad
\varepsilon_t=F(w_t)-F(w^\star),
\tag{106.18}
\]
where \(w^\star\) minimizes the convex objective on \(\mathcal C\). From (106.4), the composition \(F=\psi\circ X\) has the quadratic upper bound
\[
F(w_t)\le F(w_{t-1})
+\langle\nabla F(w_{t-1}),w_t-w_{t-1}\rangle
+\frac{L}{2n}\|X(w_t-w_{t-1})\|_2^2.
\tag{106.19}
\]
The last term is at most
\(L\gamma_t^2D_2^2/(2n)\).

The LMO is optimal for \(r_t=X^\top\alpha_t\), not for the true gradient. Compare its linear value with the value at \(w^\star\), use convexity to bound the true-gradient term by the objective gap, and apply Hölder’s inequality to the difference. Since
\[
\left|\langle X^\top(\alpha_t-\nabla\psi(Xw_{t-1})),w^\star-w_{t-1}\rangle\right|
\le D_\infty H_t,
\tag{106.20}
\]
the one-step recurrence is
\[
\varepsilon_t
\le (1-\gamma_t)\varepsilon_{t-1}
+\frac{L\gamma_t^2D_2^2}{2n}
+\gamma_tD_\infty H_t.
\tag{106.21}
\]
This is the deterministic Frank–Wolfe recurrence with one additional term. The smoothness cost is quadratic in the step; the stale-gradient cost is linear in the step and proportional to \(H_t\).

Combining (106.16) and (106.21) with
\(\gamma_t=2/(t+2)\) gives an expected primal suboptimality of order \(1/t\) for smooth convex component losses. The leading constant depends on the mapped diameters \(D_1,D_2,D_\infty\), the component smoothness \(L\), and initialization error. The data-dependent geometry can improve on a worst-case \(n\)-dependent bound, but does not guarantee dataset-size independence for every design matrix. The algorithm uses one sampled component-gradient evaluation per iteration; the quality of the rate and cost still depends on the data.

### 4.2 Worked example: sparse and dense geometries

The error-to-gap factor is \(D_\infty H_t\), while the table movement recurrence uses \(D_1\). Their ratio is informative.

First let \(X=I_n\) and let \(\mathcal C\) be the probability simplex. The difference of two feasible points has \(\ell_1\) norm at most 2 and \(\ell_\infty\) norm at most 1, with both bounds attained by distinct vertices. Thus
\[
D_1=2,\qquad D_\infty=1,\qquad D_1/D_\infty=2.
\tag{106.22}
\]
These quantities do not grow with \(n\).

For contrast, let \(\mathcal C=[0,1]\) and let every row of \(X\) equal the scalar 1. Then a feasible displacement \(\delta\) maps to
\((\delta,\ldots,\delta)\), so \(D_1=n\) and \(D_\infty=1\). The ratio is \(n\). Every example makes the same prediction change, so the total stale contribution can add coherently. One sampled update is still cheap, but its error constant can scale with the dataset size.

This comparison explains why the method’s rate is data-dependent. Sparsity or limited feature reuse can keep aggregate coordinate movement small; dense repeated features can make the bound less favorable. Reporting only “one example per iteration” omits the geometry that controls convergence.


## 5. The stochastic Frank–Wolfe gap

### 5.1 Reuse the cached derivative for a diagnostic

The true gap at \(w_{t-1}\) is
\[
G_t=\max_{s\in\mathcal C}
\langle\nabla\psi(Xw_{t-1}),X(w_{t-1}-s)\rangle.
\tag{106.23}
\]
The cached table gives a companion quantity
\[
\widehat G_t=\max_{s\in\mathcal C}
\langle\alpha_t,X(w_{t-1}-s)\rangle
=\langle r_t,w_{t-1}-s_t\rangle.
\tag{106.24}
\]
It is available from the same LMO call used to choose \(s_t\). The scalar table has therefore produced both an update direction and a diagnostic without evaluating all \(n\) losses.

For every feasible \(s\), Hölder’s inequality and the definition of \(D_\infty\) give
\[
\left|\left\langle
\alpha_t-\nabla\psi(Xw_{t-1}),X(w_{t-1}-s)
\right\rangle\right|
\le D_\infty H_t.
\tag{106.25}
\]
Taking maxima over the same feasible set preserves the uniform error:
\[
|G_t-\widehat G_t|\le D_\infty H_t.
\tag{106.26}
\]
This proof is deterministic once the table state is fixed. The stochastic analysis enters only when bounding \(H_t\).

Equation (106.26) is more informative than the generic noisy maximum in Chapter 105 because it supplies an explicit state-dependent error term. It does not make the observed gap exact, nor does it make a stochastic expectation bound into a pathwise confidence interval.

### 5.2 What the stopping statement does and does not say

Taking expectations in (106.26) yields
\[
\mathbb E|G_t-\widehat G_t|
\le D_\infty\,\mathbb E H_t.
\tag{106.27}
\]
If the right side is known and small, the stochastic gap is an expected-error proxy for the true gap. A high-probability statement can be derived from Markov’s inequality: if
\(\mathbb E|G_t-\widehat G_t|\le B_t\), then
\[
\Pr\{|G_t-\widehat G_t|\ge \eta\}\le B_t/\eta.
\tag{106.28}
\]
This bound may be conservative, and \(B_t\) must itself be available from known parameters and initialization bounds. Without such a bound, the observed gap remains a useful heuristic rather than a rigorous stopping certificate.

For the generalized-linear method of Negiar and coauthors, the cached stochastic FW gap is proposed as a heuristic stopping criterion. Their analysis bounds its discrepancy using the table error, but notes that the bound can be hard to evaluate numerically. A Lean development should preserve that distinction in its theorem names and return types: an expected discrepancy theorem is not a theorem that “small observed gap implies true gap below tolerance” on every run.


## 6. Lean proof architecture

### 6.1 Represent the state transition as a pure update

Use an immutable table \(\alpha:\mathrm{Fin}\ n\to\mathbb R\), a feature map \(a:\mathrm{Fin}\ n\to\mathbb R^d\), and an aggregate vector \(r\). A refresh operation takes a sampled index and a new scalar contribution and returns both updated fields. State the invariant \(r=\sum_i\alpha_i a_i\) separately from the stochastic error bound.

An interface sketch can make the theorem dependencies clear:

~~~lean
structure CachedFWState (n : ℕ) (d : Type*) where
  table : Fin n → ℝ
  aggregate : d
  aggregate_eq_sum : ...

def refreshCoordinate (state : CachedFWState n d)
    (i : Fin n) (newValue : ℝ) : CachedFWState n d := ...
~~~

The types in this sketch suppress the vector-space operations and finite-sum details; it is architectural pseudocode rather than a drop-in Mathlib definition. In an implementation, one may instead store a vector-valued aggregate and prove the update identity by extensionality.

### 6.2 Keep four lemmas separate

A robust formalization has at least four layers:

1. **Coordinate replacement.** Prove that the new aggregate equals the old aggregate plus the changed scalar times the sampled feature vector. This proves the invariant (106.11).
2. **Error recurrence.** For a fixed history and uniform sample, sum refreshed and stale coordinate errors and prove (106.16). Component smoothness bounds prediction movement.
3. **Oracle perturbation.** Prove (106.25) from the \(\ell_1\)-\(\ell_\infty\) inequality and mapped diameter. Taking maxima gives (106.26).
4. **Finite descent.** Combine (106.21) with the scalar recursion for \(H_t\), then solve the resulting finite sequence inequality.

This decomposition isolates data structure from analysis. The state invariant is algebraic; the recurrence uses finite uniform averaging; the oracle discrepancy is geometric; the convergence theorem is a numerical induction. The full stochastic process can be added after each one-step statement is established for a fixed history.

### 6.3 Prove the maximum perturbation once

A generic lemma should say that if two real-valued functions \(p,q\) on the same nonempty feasible set satisfy \(|p(s)-q(s)|\le \delta\) for every \(s\), then
\(|\sup_s p(s)-\sup_s q(s)|\le\delta\), assuming the suprema are finite. Then instantiate it with the two linear gap functionals and \(\delta=D_\infty H_t\). Avoid proving separate max inequalities in both directions inside the algorithm theorem; the generic lemma is useful for other approximate certificates as well.

The conditional recurrence is the probability-sensitive part. The current iterate and old table are measurable with respect to the past; the sampled index is uniform given that history. State this explicitly. An unconditional statement that the sample index is uniform overall is not enough when the state depends on earlier samples.


## 7. Common failure modes

1. **Calling the table unbiased.** Most entries are stale; the method controls a recursive error instead.
2. **Updating the table at the new iterate.** The specified refresh uses \(w_{t-1}\), before the Frank–Wolfe move.
3. **Forgetting the \(1/n\) normalization.** It appears in every cached coordinate and in the \(L/n\) smoothness constant.
4. **Recomputing \(X^\top\alpha_t\) from scratch.** The rank-one update is exact and avoids the full matrix pass.
5. **Dropping the aggregate invariant.** An incremental update is useful only if it is proved equal to the table’s linear image.
6. **Using the wrong norm pairing.** Table error is in \(\ell_1\), so the mapped feasible diameter is in \(\ell_\infty\).
7. **Replacing the data-dependent diameters by a parameter diameter.** The rates depend on \(X(\mathcal C-\mathcal C)\).
8. **Calling the gap a deterministic certificate.** A discrepancy bound involving random \(H_t\) must be controlled at the guarantee level claimed.
9. **Claiming dataset-independent convergence from constant per-step cost.** The data-dependent rate constant can still grow with \(n\).
10. **Combining state update, recurrence, and rate in one induction.** The proof has distinct invariants and should expose them separately.

## 8. Exercises

1. Derive (106.3) from the chain rule and the definition of \(\psi\).
2. Prove the aggregate invariant (106.11) by induction on the refresh operations.
3. Starting from the coordinatewise update, derive the conditional recurrence (106.16).
4. Show exactly where uniform sampling supplies the factor \(1-1/n\).
5. Derive the composition smoothness bound (106.4) from the scalar \(L\)-smoothness of each loss.
6. Prove the primal-gap recurrence (106.21), identifying the uses of convexity, oracle optimality, and mapped diameter.
7. Prove the gap discrepancy estimate (106.26) by bounding both directions between the maxima.
8. For the quadratic example, recompute the state if the second sampled index is 1 instead of 2.
9. Give a design matrix and feasible set where \(D_1/D_\infty\) grows with \(n\), and explain why the error contributions can align.
10. Suppose a known bound \(B_t\) satisfies \(\mathbb E|G_t-\widehat G_t|\le B_t\). State a high-probability error bar using Markov’s inequality and discuss when it is too weak to be useful.
11. Propose a Lean representation of the feature table that lets a single-coordinate update preserve the aggregate invariant.
12. Explain why this algorithm is related to SAGA but is not justified by simply invoking SAGA’s unbiasedness theorem.

## 9. Chapter summary

Generalized linear finite sums expose a useful coordinate structure: the full gradient is \(X^\top\) applied to scalar loss derivatives. Stochastic Frank–Wolfe refreshes one derivative coordinate, updates the aggregate gradient exactly by a rank-one term, and applies an LMO to that cached aggregate.

The table is stale rather than conditionally unbiased. Uniform refreshing and smoothness yield a recursive error bound; mapped data diameters convert it into a descent error and a gap-estimation error. Under the method’s smooth convex assumptions and decreasing step schedule, the expected objective gap is \(O(1/t)\) with data-dependent constants. The sampled FW gap is an expected-error proxy, and becomes a reliable stopping rule only when an appropriate error bound is available. In Lean, formalize the aggregate invariant, stale-table recurrence, oracle perturbation, and scalar convergence argument as separate results.

## Further reading

- Negiar et al., [“Stochastic Frank-Wolfe for Constrained Finite-Sum Minimization”](https://proceedings.mlr.press/v119/negiar20a.html), including the supplementary proof of the one-coordinate update, error recurrence, and gap discrepancy.
- Chapter 105, for generic finite-sum variance reduction and the bias of a sampled maximum gap.
- Chapters 98, 103, and 104, for deterministic FW geometry, nonconvex gaps, and general noisy-oracle analysis.

