# Chapter 101 — Pairwise Frank–Wolfe and Sparse Support Transfers

> **Audience.** This chapter assumes the global linear-oracle and active-set methods from Chapters 98–100. It develops pairwise Frank–Wolfe (PFW), which moves weight directly from an active atom to a globally improving atom.

An away step changes one active weight by redistributing its mass proportionally across the other active atoms. A fully corrective step solves a restricted optimization problem over many atoms. Pairwise Frank–Wolfe uses a smaller operation: it transfers mass from one active atom to one new or existing atom.

This direct transfer can prune an unwanted atom without altering unrelated coefficients. It is attractive when sparse support matters and weight updates are cheap. Its analysis has a complication that AFW avoids: a maximal pairwise step can replace one atom with another without decreasing the size of the active set. Such a swap step is feasible and can make substantial progress, but the standard global linear-rate proof has a much weaker iteration count.

## Learning objectives

After this chapter, you should be able to:

- define the toward and away atoms and derive the pairwise gap identity;
- update a convex representation by transferring mass between two atoms;
- distinguish drop, swap, and interior steps;
- maintain feasibility and support invariants for a pairwise update;
- state the known global rate and explain why its swap-step count is conservative;
- organize Lean proofs around transfer algebra, oracle certificates, and a separate counting theorem.

## 1. Transfer mass between two atoms

### 1.1 The two oracle choices

Let the feasible polytope be \(P=\operatorname{conv}(A)\), with finite atom set \(A\). Maintain a convex representation

\[
x_t=\sum_{v\in S_t}\lambda_v^{(t)}v,
\qquad
\lambda_v^{(t)}>0,\qquad
\sum_{v\in S_t}\lambda_v^{(t)}=1.
\tag{101.1}
\]

At \(x_t\), let \(g_t=\nabla f(x_t)\). The global toward atom minimizes the gradient pairing:

\[
s_t\in\arg\min_{s\in A}\langle g_t,s\rangle.
\tag{101.2}
\]

The away atom maximizes it over the active support:

\[
v_t\in\arg\max_{v\in S_t}\langle g_t,v\rangle.
\tag{101.3}
\]

The first search asks which feasible atom is best over the entire polytope. The second asks which currently represented atom is worst to keep. Both searches are essential: without the global oracle, the method cannot discover a missing good atom; without the active set, it cannot identify a coefficient from which mass can be removed.

### 1.2 The pairwise gap

Define the toward and away gaps as in Chapter 99:

\[
g_t^{\mathrm{FW}}=\langle g_t,x_t-s_t\rangle,
\qquad
g_t^{\mathrm A}=\langle g_t,v_t-x_t\rangle.
\tag{101.4}
\]

The pairwise direction is

\[
d_t^{\mathrm{PFW}}=s_t-v_t,
\tag{101.5}
\]
and its gap satisfies the exact identity

\[
g_t^{\mathrm{PFW}}
:=\langle g_t,v_t-s_t\rangle
=g_t^{\mathrm{FW}}+g_t^{\mathrm A}.
\tag{101.6}
\]

The directional derivative along \(d_t^{\mathrm{PFW}}\) is \(-g_t^{\mathrm{PFW}}\), so it is a descent direction whenever the pairwise gap is positive. Unlike AFW, PFW does not compare the two gaps and then choose one direction. It combines them into a single transfer.

If \(s_t=v_t\), the pairwise direction and gap are zero. The current point is already optimal for the linearization over the polytope: the global minimizing atom is also an active atom maximizing the gradient on the support. This is a stopping case for the exact gap test.

### 1.3 The coefficient update

For \(s_t\ne v_t\), choose \(0\le\gamma_t\le\lambda_{v_t}^{(t)}\) and update

\[
x_{t+1}=x_t+\gamma_t(s_t-v_t).
\tag{101.7}
\]

Only two coefficients change:

\[
\lambda_{v_t}^{(t+1)}
=\lambda_{v_t}^{(t)}-\gamma_t,
\qquad
\lambda_{s_t}^{(t+1)}
=\lambda_{s_t}^{(t)}+\gamma_t.
\tag{101.8}
\]

All other coefficients stay the same. If \(s_t\) already belongs to the support, its old coefficient is increased. Otherwise it receives a new positive coefficient. The update preserves the total mass because one coefficient loses exactly what the other gains. The step bound preserves nonnegativity of the away coefficient.

This algebra is simpler than the AFW weight update in Chapter 99: there is no common scaling of the remaining weights. The price is a more complicated support history, because the new atom may enter at the same instant that the old atom leaves.

## 2. Step types and support behavior

### 2.1 Interior pairwise steps

If \(\gamma_t<\lambda_{v_t}^{(t)}\), the away coefficient remains positive. If \(s_t\) was already active, the support is unchanged. If \(s_t\) was new, the support grows by one. An interior step never removes the away atom.

A line search chooses a minimizer of
\[
\gamma\mapsto f(x_t+\gamma(s_t-v_t))
\quad\text{over}\quad
[0,\lambda_{v_t}^{(t)}].
\tag{101.9}
\]
Since \(\gamma=0\) is allowed, the objective cannot increase. Smoothness gives a quadratic upper bound along this segment, while the pairwise gap supplies its initial negative slope.

### 2.2 Drop steps and swap steps

At the endpoint \(\gamma_t=\lambda_{v_t}^{(t)}\), the away coefficient becomes zero. If \(s_t\) was already active, its coefficient increases and the support loses \(v_t\); this is a **drop step**. If \(s_t\) was not active, it receives the transferred mass at the same time that \(v_t\) is removed. The support cardinality is unchanged; this is a **swap step**.

A swap is not a failure. It may give a large objective decrease and can rapidly move the representation toward a useful face. Its difficulty is for the proof: support size alone does not show that swaps are infrequent. A drop decreases support, but a swap can replace one vertex by another while leaving the number of active vertices fixed.

For a finite atom set, there are only finitely many supports and transfer states in a suitable combinatorial accounting. The established PFW convergence proof uses that finiteness to bound how many problematic swaps may occur before enough good steps are guaranteed. The resulting worst-case count is extremely conservative. It is a theorem about the worst case, not a prediction that observed optimization will take factorially many iterations.

## 3. Work the transfers by hand

### 3.1 A direct removal on the simplex

Consider the probability simplex with vertices \(e_1,e_2,e_3\), current point

\[
x=0.55e_1+0.35e_2+0.10e_3,
\]

and gradient \(g=(-1,0,2)\). The global linear oracle chooses \(s=e_1\), while the active-set maximizer chooses \(v=e_3\). The pairwise gap is

\[
g^{\mathrm{PFW}}=\langle g,e_3-e_1\rangle=2-(-1)=3.
\]

Take a maximal step \(\gamma=0.10\), exactly the weight on \(e_3\). The update transfers that mass to \(e_1\):

\[
(0.55,0.35,0.10)\longmapsto(0.65,0.35,0).
\]

The total remains one, all coefficients are nonnegative, and the support loses \(e_3\). For the linear objective with this fixed gradient, the objective change is
\(\gamma\langle g,s-v\rangle=-0.30\), matching the pairwise gap times the step size. This example illustrates the update; the convergence theorem requires a smooth strongly convex objective, not this linear one.

### 3.2 A maximal swap need not shrink support

Let

\[
x=0.2e_1+0.8e_2,\qquad g=(1,2,0).
\]

The global minimizing atom is \(s=e_3\), and the away atom among the support is \(v=e_2\). The pairwise gap equals \(2\). A maximal step has size \(0.8\), yielding

\[
(0.2,0.8,0)\longmapsto(0.2,0,0.8).
\]

The active set changes from \(\{e_1,e_2\}\) to \(\{e_1,e_3\}\), so its size remains two. This is a swap step. With a linear objective whose gradient is \(g\), the objective decreases by \(0.8\cdot2=1.6\), despite no support-size decrease.

The example explains why support cardinality is an incomplete progress measure for PFW. A formal proof that tracks only \(|S_t|\) will classify this iteration as neither a support growth nor a support decrease, even though both the represented point and the active atom identities change.

The two rational updates can be checked with one transfer function. In the first, the away weight disappears and total mass is preserved. In the second, the old away atom is replaced by a new atom, so support size stays constant.

```lean
import Book.Models.FiniteOptimization

open Book.Models.FiniteOptimization

theorem pairwise_update_conserves_mass :
    pairMass (transferOne 2 1).1 (transferOne 2 1).2 = pairMass 2 1 := by decide

theorem pairwise_update_stays_nonnegative : (transferOne 2 1).1 ≥ 0 := by decide

def pairwiseTransfer101 (weights : Fin 3 → ℚ) (away toward : Fin 3)
    (gamma : ℚ) (i : Fin 3) : ℚ :=
  if i = away then weights i - gamma
  else if i = toward then weights i + gamma
  else weights i

def dropWeights101 : Fin 3 → ℚ := fun i =>
  if i = 0 then 11 / 20 else if i = 1 then 7 / 20 else 1 / 10

theorem pairwise_drop_update_exact :
    pairwiseTransfer101 dropWeights101 2 0 (1 / 10) =
      fun i => if i = 0 then 13 / 20 else if i = 1 then 7 / 20 else 0 := by
  funext i
  fin_cases i <;> norm_num [pairwiseTransfer101, dropWeights101]

theorem pairwise_drop_preserves_mass :
    (∑ i : Fin 3, pairwiseTransfer101 dropWeights101 2 0 (1 / 10) i) = 1 := by
  norm_num [Fin.sum_univ_succ, pairwiseTransfer101, dropWeights101]

theorem pairwise_drop_removes_away_atom :
    pairwiseTransfer101 dropWeights101 2 0 (1 / 10) 2 = 0 := by
  norm_num [pairwiseTransfer101, dropWeights101]

def swapWeights101 : Fin 3 → ℚ := fun i =>
  if i = 0 then 1 / 5 else if i = 1 then 4 / 5 else 0

theorem pairwise_swap_update_exact :
    pairwiseTransfer101 swapWeights101 1 2 (4 / 5) =
      fun i => if i = 0 then 1 / 5 else if i = 1 then 0 else 4 / 5 := by
  funext i
  fin_cases i <;> norm_num [pairwiseTransfer101, swapWeights101]

theorem pairwise_swap_preserves_mass :
    (∑ i : Fin 3, pairwiseTransfer101 swapWeights101 1 2 (4 / 5) i) = 1 := by
  norm_num [Fin.sum_univ_succ, pairwiseTransfer101, swapWeights101]

theorem pairwise_swap_replaces_away_atom :
    pairwiseTransfer101 swapWeights101 1 2 (4 / 5) 1 = 0 ∧
      0 < pairwiseTransfer101 swapWeights101 1 2 (4 / 5) 2 := by
  norm_num [pairwiseTransfer101, swapWeights101]
```

### 3.3 The step bound is representation-dependent

The maximal pairwise step is the chosen coefficient \(\lambda_{v_t}^{(t)}\). It is the largest transfer that keeps the same representation nonnegative while moving mass only from \(v_t\) to \(s_t\). A different convex representation of the same point could give a different away atom or a different maximum step.

This local bound does not claim to be the largest distance one could travel along the line while remaining in the polytope. Determining that distance for a general polytope may require a stronger feasibility oracle than the LMO. PFW chooses the bound that its stored weights can certify directly.

## 4. Convergence and its swap-step caveat

### 4.1 Good-step contraction

Use the assumptions from Chapter 99: \(f\) is \(\mu\)-strongly convex and has \(L\)-Lipschitz gradient on the required domain, \(P=\operatorname{conv}(A)\) is a finite polytope, \(D=\operatorname{diam}(P)\), and its pyramidal width is \(\delta>0\). Set

\[
\rho=\frac{\mu}{4L}\left(\frac{\delta}{D}\right)^2.
\tag{101.10}
\]

The pairwise gap is the sum of the toward and away gaps, so the chosen pairwise direction aligns with the negative gradient at least as well as either component alone. The same smoothness and geometric argument as in Chapter 99 gives, on every good step,

\[
h_{t+1}\le(1-\rho)h_t,
\qquad h_t=f(x_t)-f(x^\star).
\tag{101.11}
\]

A good step is one that does not hit the maximal transfer bound. At a maximal step, the update may still make progress, as the examples show, but the standard proof does not guarantee the same contraction factor.

If \(k(t)\) denotes the number of good steps among the first \(t\) iterations, then

\[
h_t\le(1-\rho)^{k(t)}h_0
\le e^{-\rho k(t)}h_0.
\tag{101.12}
\]

The key analytic estimate is not special to PFW. The difference from AFW and FCFW lies in how one proves a lower bound on \(k(t)\).

### 4.2 A conservative global count

For AFW, every drop step decreases support, and a toward step can add at most one atom, giving a direct count when the run starts at a vertex. FCFW uses correction certificates to guarantee progress every outer step. PFW has swap steps: the away atom leaves while a new toward atom enters, so the support size does not change.

For a finite atom set \(A\), Lacoste-Julien and Jaggi prove the conservative bound

\[
k(t)\ge \frac{t}{3|A|!+1}.
\tag{101.13}
\]

Consequently \(h_t\le h_0\exp\bigl(-\rho t/(3|A|!+1)\bigr)\). The factorial makes this global guarantee much weaker than AFW’s good-step count, especially when \(A\) is large. It should be presented as a worst-case theorem, not as a practical iteration estimate.

The bound still establishes global linear convergence under the stated assumptions. In practice, PFW may perform well when sparse support is valuable: it transfers mass directly to a promising atom and can prune an unwanted coordinate without rescaling the rest. The computational choice depends on the cost of tracking and updating the representation, not on the rate theorem alone.

## 5. Lean proof architecture

### 5.1 Make transfer algebra a standalone layer

Represent weights over a finite vertex type or a finitely supported atom map. Define a transfer update that subtracts \(\gamma\) at \(v\), adds \(\gamma\) at \(s\), and leaves all other coordinates unchanged. Prove these facts before introducing the objective:

1. the weight sum is preserved;
2. the step bound gives a nonnegative coefficient at \(v\);
3. the toward coefficient remains nonnegative;
4. the represented point changes by \(\gamma(s-v)\);
5. no unrelated coefficient changes.

Use an explicit case split for \(s=v\). In that case a transfer is the zero direction, and the algorithm should stop or choose a zero step rather than invoke a maximal transfer based on the same coefficient as both source and destination.

For support theorems, prove two separate cases. If \(s\) is already active and \(\gamma=\lambda_v\), the support loses \(v\) (assuming \(s\ne v\)). If \(s\) is new and \(\gamma=\lambda_v\), the old \(v\) is removed and \(s\) is added, preserving support cardinality. Encoding these cases in a single opaque theorem tends to obscure the swap.

### 5.2 Separate the oracle and line-search interfaces

The global oracle certificate proves \(s_t\) minimizes the gradient pairing over all atoms. The active maximizer certificate proves \(v_t\) maximizes it over the active support. Together they establish nonnegativity of both component gaps and the identity (101.6).

A line-search result should contain a feasible step \(\gamma_t\), its interval bound, and an objective comparison with every feasible step on the pairwise segment. A smoothness lemma then converts the pairwise gap and selected step into a decrease estimate. Keep the line-search implementation opaque to this theorem: exact symbolic minimization, one-dimensional convex search, or a certified inexact procedure can all produce the same certificate.

### 5.3 Isolate swap counting from contraction

The active-set identities are finite combinatorics; the good-step contraction is real analysis. Do not make the analytic recurrence inspect support sets. Instead, prove a combinatorial theorem that takes an abstract run with drop, swap, and good labels and returns the lower bound on the number of good steps. The scalar theorem then consumes only that count and the contraction factor.

A suitable proof dependency structure is:

~~~text
finite weight transfer ──> feasibility and support cases
global LMO + active max ──> pairwise gap identity
line-search + smoothness ─> good-step contraction
drop/swap combinatorics ──> lower bound on good-step count
             scalar recurrence + good-step count
                            |
                            v
                  global objective-gap rate
~~~

This modularity permits the pairwise counting theorem to change without rewriting the inner-product and smoothness proofs.

## 6. Common failure modes

1. **Updating all coefficients as in AFW.** Pairwise Frank–Wolfe changes only the toward and away coefficients.
2. **Using an away atom outside the active support.** The transfer source needs positive current weight.
3. **Forgetting the global oracle search.** A restricted minimizer over the active set cannot find an undiscovered improving atom.
4. **Allowing \(\gamma>\lambda_v\).** The away coefficient becomes negative, invalidating the convex representation.
5. **Conflating a drop with a swap.** Both set the old away weight to zero; a swap also adds a previously inactive atom.
6. **Using support size as the only progress measure.** A swap preserves cardinality while changing the represented point.
7. **Applying good-step contraction at a maximal transfer without proof.** The examples show objective decrease, but not the uniform theorem factor.
8. **Claiming the factorial count is a practical prediction.** It is a conservative worst-case guarantee.
9. **Ignoring duplicate atoms or \(s=v\).** The zero-direction case needs explicit handling.
10. **Mixing weight arithmetic with pyramidal-width analysis.** Prove transfer invariants first, then consume them through a descent interface.

## 7. Exercises

1. Derive the pairwise-gap identity (101.6) from the definitions of the toward and away gaps.
2. Prove that the transfer in (101.8) preserves the sum of all weights.
3. Prove feasibility of the new representation when \(0\le\gamma\le\lambda_v\) and \(s\ne v\).
4. For the first simplex example, compute the old and new values of the linear objective.
5. For the second example, verify the pairwise gap and show explicitly why support cardinality is unchanged.
6. State a Lean proposition for the update of the weighted point and prove it from finite sums.
7. Explain why a point can have two different active representations with distinct pairwise step limits.
8. Prove that an interior pairwise step adds at most one support element and removes none.
9. Describe an abstract inductive state sufficient to count good, drop, and swap steps without mentioning vectors.
10. Given a good-step lower bound \(k(t)\), derive the objective-error estimate (101.12).
11. Compare AFW and PFW updates when the selected toward atom already belongs to the active support.
12. Explain which parts of the PFW proof change if the linear oracle is only approximate.

## 8. Chapter summary

Pairwise Frank–Wolfe transfers weight directly from an active away atom to a globally improving toward atom. Its update preserves the convex representation while changing only two coefficients. This can make sparse support management attractive, and maximal steps may either drop an atom or swap it for a new one.

Smoothness and pyramidal width give the same contraction on good steps as other linear Frank–Wolfe variants. The global rate proof is weaker because swaps are harder to count; the established finite-atom guarantee has a factorial dependence. In Lean, isolate transfer arithmetic, oracle certificates, line-search descent, and swap counting so that the combinatorial limitation remains separate from the analytic core.

## Further reading

- Lacoste-Julien and Jaggi, [“On the Global Linear Convergence of Frank–Wolfe Optimization Variants”](https://proceedings.neurips.cc/paper_files/paper/2015/file/c058f544c737782deacefa532d9add4c-Paper.pdf), for PFW’s transfer update, swap steps, and convergence bound.
- Chapter 99 — Away-Step Frank–Wolfe and Linear Convergence, for away-weight updates and drop-step counting.
- Chapter 100 — Fully Corrective Frank–Wolfe and Active-Set Optimization, for correction hulls and per-iteration progress certificates.

