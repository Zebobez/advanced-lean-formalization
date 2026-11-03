# Chapter 99 — Away-Step Frank–Wolfe and Linear Convergence

> **Audience.** This chapter assumes the linear-oracle and curvature interfaces from Chapter 98, along with strong convexity and smoothness from Chapters 90–93. It studies how an explicit convex decomposition lets a projection-free method remove atoms that no longer belong in a useful representation.

Standard Frank–Wolfe adds one atom at a time but never directly decreases the weight of an existing atom. When the minimizer lies on a low-dimensional face of a polytope, the iterate may carry positive weight on vertices outside that face for many iterations. Away-step Frank–Wolfe (AFW) adds a second kind of move: it can travel away from a currently active vertex and reduce its weight all the way to zero.

That extra state supports a stronger convergence theorem. For a smooth, strongly convex objective on a finite polytope, AFW has a global linear rate under a positive geometric condition on the polytope. The proof is a good case study in advanced formalization: active-set updates are finite algebra, the one-step decrease is analytic, and the rate depends on a geometric theorem that should be isolated behind its own interface.

## Learning objectives

After this chapter, you should be able to:

- maintain a convex decomposition and derive both toward and away updates;
- define the away vertex, the two gaps, and the feasible away step interval;
- prove that a maximal away step removes an atom from the active set;
- explain why drop steps do not destroy the global linear rate;
- state the pyramidal-width convergence theorem with its assumptions;
- design Lean declarations that separate finite support bookkeeping from analytic convergence.

## 1. Why add an away direction?

### 1.1 The boundary problem

Suppose the feasible set is the convex hull of a finite set of atoms \(A\), and the current iterate has a representation

\[
x_t=\sum_{v\in S_t}\lambda_v^{(t)}v,
\qquad \lambda_v^{(t)}>0,
\qquad \sum_{v\in S_t}\lambda_v^{(t)}=1.
\tag{99.1}
\]

Here \(S_t\subseteq A\) is the active set for this particular representation. A standard Frank–Wolfe update moves toward a new oracle atom \(s_t\). It scales every old weight by \(1-\gamma_t\), then assigns weight \(\gamma_t\) to \(s_t\). The method is sparse, but its only direct way to reduce the weight of an old atom is to scale all old weights together.

That can be inefficient near a face. If the optimizer lies on a face that excludes an old atom, the method may repeatedly move toward vertices in the face without promptly eliminating the outside atom. This is the familiar zig-zagging picture from Chapter 98. An away step selects one active atom and decreases its weight relative to all the other weights.

Away steps are available precisely because the algorithm stores a decomposition. A point alone does not identify which atom should be removed. Different convex decompositions of the same point can give different candidate away vertices, and consequently different step bounds.

### 1.2 The active set is algorithmic state

The active set is not necessarily the smallest set whose convex hull contains \(x_t\). It is the support of the decomposition that the algorithm actually maintains. In a simplex, barycentric coordinates are unique. In a general polytope, a point can have many representations, and one representation can contain redundant atoms.

For correctness, maintain a package of facts:

1. every active atom belongs to \(A\);
2. every active weight is positive;
3. the weights sum to one;
4. their weighted sum is the current iterate.

The iterate is feasible because it is a convex combination of feasible atoms. The algorithmic state carries more information than feasibility alone, but this extra information is what makes away moves possible.

## 2. The two candidate directions

### 2.1 The Frank–Wolfe atom and gap

Write \(g_t=\nabla f(x_t)\). A linear minimization oracle returns an atom

\[
s_t\in\arg\min_{s\in A}\langle g_t,s\rangle.
\tag{99.2}
\]

The toward direction is \(d_t^{\mathrm{FW}}=s_t-x_t\), and its gap is

\[
g_t^{\mathrm{FW}}
=\langle g_t,x_t-s_t\rangle\ge0.
\tag{99.3}
\]

The nonnegativity follows because \(x_t\) is a convex combination of atoms and the oracle minimizes the linear functional over all atoms. The direction has directional derivative \(\langle g_t,d_t^{\mathrm{FW}}\rangle=-g_t^{\mathrm{FW}}\).

### 2.2 The away atom and gap

Choose an active atom \(v_t\) maximizing the gradient pairing over the active set:

\[
v_t\in\arg\max_{v\in S_t}\langle g_t,v\rangle.
\tag{99.4}
\]

The away direction points from this atom back toward the current iterate:

\[
d_t^{\mathrm A}=x_t-v_t,
\qquad
g_t^{\mathrm A}=\langle g_t,v_t-x_t\rangle\ge0.
\tag{99.5}
\]

The inequality follows because \(x_t\) is an average of active atoms and \(v_t\) maximizes the pairing among them. Again, the directional derivative is negative:
\(\langle g_t,d_t^{\mathrm A}\rangle=-g_t^{\mathrm A}\).

Both gaps are descent certificates, but they refer to different searches. The Frank–Wolfe search ranges over all atoms in \(A\). The away search ranges only over the current active set \(S_t\), which is usually much smaller. AFW selects whichever candidate gap is larger. It takes a toward step when \(g_t^{\mathrm{FW}}\ge g_t^{\mathrm A}\), and an away step otherwise.

The comparison is essential. Always taking the away direction could discard a useful atom; always taking the toward direction reduces the method to standard Frank–Wolfe.

### 2.3 Feasible step intervals

A toward update is
\[
x_{t+1}=x_t+\gamma(s_t-x_t),
\qquad 0\le\gamma\le1.
\tag{99.6}
\]
It is a convex combination of \(x_t\) and \(s_t\), so it stays in the polytope.

An away update is
\[
x_{t+1}=x_t+\gamma(x_t-v_t)
=(1+\gamma)x_t-\gamma v_t.
\tag{99.7}
\]
If \(v_t\) has current weight \(\lambda_{v_t}^{(t)}\), the corresponding updated weights are

\[
\lambda_u^{(t+1)}=(1+\gamma)\lambda_u^{(t)}
\quad (u\ne v_t),\qquad
\lambda_{v_t}^{(t+1)}
=(1+\gamma)\lambda_{v_t}^{(t)}-\gamma.
\tag{99.8}
\]

Their sum remains one. Nonnegativity of the away weight is equivalent to

\[
0\le\gamma\le\gamma_{\max}^{\mathrm A}
:=\frac{\lambda_{v_t}^{(t)}}{1-\lambda_{v_t}^{(t)}}.
\tag{99.9}
\]

For an active set with more than one positive weight, \(0<\lambda_{v_t}^{(t)}<1\), so this bound is well-defined. At \(\gamma=\gamma_{\max}^{\mathrm A}\), the selected weight becomes zero. This is a **drop step**: remove \(v_t\) from the active set. If the active set has just one atom, the away direction is zero and the algorithm should not treat that atom as a valid away choice.

The bound in (99.9) is the largest step that preserves this chosen decomposition by the update (99.8). For a redundant representation, it need not be the largest step that would keep the point feasible by some entirely different decomposition. The conservative bound is useful because its proof is local and it preserves the tracked representation.

After choosing a direction, AFW performs a line search on its feasible interval: \([0,1]\) for a toward step and \([0,\gamma_{\max}^{\mathrm A}]\) for an away step. Exact line search ensures that the objective does not increase, since the zero step is available. A step that reaches its endpoint and shrinks the active set is recorded as a drop step; an interior step is a good step for the rate argument. Variants that use an inexact line search need a sufficient-decrease guarantee in place of exact minimization.

## 3. Work the updates by hand

### 3.1 An away step can remove a stale atom

Let \(A=\{e_1,e_2,e_3\}\) be the vertices of the probability simplex, and minimize the linear function \(f(x)=-x_1\). At

\[
x=0.99e_1+0.01e_2,
\]

the gradient is \(g=(-1,0,0)\). The Frank–Wolfe oracle chooses \(s=e_1\), so

\[
g^{\mathrm{FW}}
=\langle g,x-e_1\rangle=0.01.
\]

The active atom with maximal gradient pairing is \(v=e_2\). Its away gap is

\[
g^{\mathrm A}
=\langle g,e_2-x\rangle=0.99.
\]

AFW chooses the away direction \(x-e_2\). The maximum away step is \(0.01/(1-0.01)=1/99\), and the update gives

\[
x+\frac{1}{99}(x-e_2)=e_1.
\]

The coefficient of \(e_2\) becomes zero, so the algorithm removes it. This linear objective is used only to illustrate the state update; a linear function is not strongly convex, so the linear-convergence theorem below does not apply to this example.

### 3.2 Verify a drop-step calculation

Consider any three atoms \(a,b,c\) with weights \((0.5,0.3,0.2)\), and suppose \(c\) is selected for an away step. Then

\[
\gamma_{\max}^{\mathrm A}=\frac{0.2}{0.8}=\frac14.
\]

At the maximal step, the new weights are

\[
\left(\frac54\cdot0.5,\frac54\cdot0.3,
\frac54\cdot0.2-\frac14\right)
=(0.625,0.375,0).
\tag{99.10}
\]

They remain nonnegative and sum to one. The new iterate is \(0.625a+0.375b\), and \(c\) leaves the active set. The key invariant is algebraic: all nonselected weights are scaled by the same positive factor, while exactly the chosen weight reaches zero.

A pairwise Frank–Wolfe step combines the two choices into one direction \(s_t-v_t\). Its maximal step is the away weight \(\lambda_{v_t}^{(t)}\): mass moves directly from the away atom to the toward atom. This variant can preserve sparsity particularly well, but it has swap steps where one weight reaches zero and another is added. Its convergence bookkeeping is more delicate, so the main theorem here concerns AFW.

The following rational calculation checks the three-atom drop step in equation 99.10. It verifies the updated weights explicitly and confirms that they still sum to one.

```lean
import Book.Models.FiniteOptimization

open Book.Models.FiniteOptimization

theorem away_step_preserves_pair_mass :
    pairMass (transferOne 1 1).1 (transferOne 1 1).2 = 2 := by decide

theorem away_step_removes_one_unit_from_donor :
    (transferOne 2 1).1 = 1 := by decide

def awayWeights99 : Fin 3 → ℚ := fun i =>
  if i = 0 then 1 / 2 else if i = 1 then 3 / 10 else 1 / 5

def awayWeightUpdate99 (weights : Fin 3 → ℚ) (away : Fin 3)
    (gamma : ℚ) (i : Fin 3) : ℚ :=
  if i = away then (1 + gamma) * weights i - gamma
  else (1 + gamma) * weights i

theorem away_weights_initial_sum : (∑ i : Fin 3, awayWeights99 i) = 1 := by
  norm_num [Fin.sum_univ_succ, awayWeights99]

theorem away_drop_weights_exact :
    awayWeightUpdate99 awayWeights99 2 (1 / 4) =
      fun i => if i = 0 then 5 / 8 else if i = 1 then 3 / 8 else 0 := by
  funext i
  fin_cases i <;> norm_num [awayWeightUpdate99, awayWeights99]

theorem away_drop_weights_sum :
    (∑ i : Fin 3, awayWeightUpdate99 awayWeights99 2 (1 / 4) i) = 1 := by
  norm_num [Fin.sum_univ_succ, awayWeightUpdate99, awayWeights99]
```

## 4. Why active-set removal gives a linear rate

### 4.1 The role of polytope geometry

Strong convexity controls objective error in terms of distance and gradient alignment. Smoothness converts a directional gap into objective decrease. The missing ingredient is a lower bound on how well an available toward/away direction aligns with the optimal error direction.

For polytopes, Lacoste-Julien and Jaggi use **pyramidal width**, a positive geometric constant \(\delta\) determined by the atom set and its faces. Intuitively, it prevents every feasible direction and every active representation from becoming arbitrarily narrow at the same time. It plays the role of a condition parameter for the constraint set. Let \(D\) be the Euclidean diameter of the polytope. A small ratio \(\delta/D\) means the domain geometry is poorly conditioned; a larger ratio supports faster convergence.

The full definition takes a minimum over feasible directions and active-set representations on faces. It is not simply the shortest edge length or the minimum width of the whole polytope. For formalization, one should use the published definition or a proved equivalent characterization rather than replace it with an intuitive proxy.

### 4.2 A one-step decrease argument

Let \(h_t=f(x_t)-f(x^\star)\), and write \(r_t=-\nabla f(x_t)\) and \(e_t=x^\star-x_t\). Strong convexity yields the useful estimate

\[
h_t\le
\langle r_t,e_t\rangle-\frac{\mu}{2}\|e_t\|^2
\le \frac{\langle r_t,e_t\rangle^2}{2\mu}.
\tag{99.11}
\]

The second inequality maximizes the quadratic expression over the possible value of \(\|e_t\|\). On the other hand, \(L\)-smoothness gives, for an available direction \(d\) and feasible \(\gamma\),

\[
f(x_t+\gamma d)
\le f(x_t)+\gamma\langle\nabla f(x_t),d\rangle
+\frac{L\gamma^2}{2}\|d\|^2.
\tag{99.12}
\]

If the minimizing step of the quadratic upper bound lies in the feasible interval, this implies decrease at least
\(\langle r_t,d\rangle^2/(2L\|d\|^2)\). Pyramidal width lower-bounds the best pairwise gap relative to \(\langle r_t,e_t\rangle\). The chosen AFW gap is at least half that pairwise gap, because the pairwise gap is the sum of the toward and away gaps and AFW chooses the larger. Squaring this factor of one half produces the factor \(1/4\) in the rate.

This argument applies directly to a good step, where the curvature-optimal step is feasible. A drop step can be truncated by the active-weight constraint and may not satisfy the same progress estimate. The point is not to pretend every iteration decreases by the same factor. Instead, prove the rate on good steps and count how often drop steps can occur.

### 4.3 The global linear-convergence theorem

Let \(P=\operatorname{conv}(A)\) be a polytope generated by a finite atom set. Assume \(f\) is \(\mu\)-strongly convex on \(P\), and its gradient is \(L\)-Lipschitz on the domains needed for the toward and away segments (in the cited AFW analysis, a sufficient domain is \(P+P-P\)). Let \(D=\operatorname{diam}(P)\), and let \(\delta=\operatorname{PWidth}(A)>0\) be the pyramidal width. Define

\[
\rho=\frac{\mu}{4L}\left(\frac{\delta}{D}\right)^2.
\tag{99.13}
\]

For each good step, the objective gap contracts:

\[
h_{t+1}\le(1-\rho)h_t.
\tag{99.14}
\]

For AFW initialized at a vertex and maintaining its active representation, drop steps can occur no more than half the time. Thus among the first \(t\) iterations there are at least \(k(t)\ge t/2\) good steps, and

\[
h_t\le(1-\rho)^{k(t)}h_0
\le \exp(-\rho k(t))h_0
\le \exp(-\rho t/2)h_0.
\tag{99.15}
\]

The exponent can be stated with integer floors when writing a fully discrete theorem. A linear rate means that a fixed multiplicative factor smaller than one applies after a bounded number of iterations; it does not mean the error decreases by a fixed additive amount.

The theorem clarifies what AFW does and does not promise. Strong convexity alone is not enough for the standard Frank–Wolfe method to achieve this rate when the optimum is on the boundary. AFW adds active-set removal, while pyramidal width quantifies whether the polytope provides a direction with sufficient alignment. If the objective is merely convex, the strong-convexity term disappears and the same statement does not imply a geometric rate.

### 4.4 A numerical reading of the rate

Suppose a problem has \(\mu=2\), \(L=4\), diameter \(D=3\), and pyramidal width \(\delta=1\). Then \(\rho=1/72\). Ten AFW iterations starting at a vertex contain at least five good steps, so the theorem gives

\[
h_{10}\le\left(\frac{71}{72}\right)^5 h_0
\le \exp(-5/72)h_0.
\tag{99.16}
\]

The bound is conservative: it uses the worst-case geometry of the whole polytope and counts only guaranteed good steps. Its value is explanatory as well as quantitative. The objective condition number \(L/\mu\) and the geometric condition ratio \(D/\delta\) contribute independently to the convergence constant.

## 5. Lean proof architecture

### 5.1 Represent the active state explicitly

For a finite vertex type \(V\) and a real inner-product space \(E\), one convenient design stores a weight function on \(V\), a vertex map, and the represented point. The core invariants are:

- each weight is nonnegative;
- the weights sum to one;
- the point equals the weighted sum of vertices;
- the active set consists exactly of vertices with positive weight.

A finite type makes sums straightforward, though a finite-support map is often more suitable when the global atom type is infinite. The choice is an API decision: a finite Fintype is convenient for a fixed polytope, while a finitely supported weight map captures sparse iterates in a larger atom universe.

Do not define active membership as “appears in some decomposition.” That existential set is too large for the update proof. Define it from the chosen weight state.

### 5.2 Prove update algebra before optimization

Package the state update as a transformation on weights. For a toward step, define

\[
\lambda'_u=(1-\gamma)\lambda_u+\gamma\,\mathbf{1}_{u=s}.
\tag{99.17}
\]

For an away step at \(v\), use (99.8). Prove small lemmas first:

1. the updated weights sum to one;
2. the step bound implies every updated weight is nonnegative;
3. the weighted vertex sum equals the claimed point update;
4. at the maximal away step, the weight of \(v\) is zero;
5. other positive weights remain positive when the away step is nonzero.

The last claim uses \(1+\gamma>0\). These statements are linear arithmetic once the representation invariant is available. They should not depend on differentiability or convexity.

A useful Lean decomposition has a record for the active representation and separate update functions for toward and away moves. Then theorems about weightSum, point_eq_weighted_sum, and active_after_drop can be tested independently of the convergence proof. The invariant proof is the right place for finite-sum manipulation and field_simp; the analytic theorem should never unfold those definitions.

### 5.3 Separate oracle facts and descent facts

Use one certificate for the global linear minimization oracle and another for the active-set maximizer. Their conclusions have opposite inequalities:

\[
\langle g,s_t\rangle\le\langle g,u\rangle
\quad(u\in A),\qquad
\langle g,v_t\rangle\ge\langle g,u\rangle
\quad(u\in S_t).
\tag{99.18}
\]

From these certificates and the convex representation, prove both gaps are nonnegative. Then prove the direction derivative identities. This gives an algorithm-independent local theorem:

> whichever direction AFW selects, its directional derivative is the negative of the selected nonnegative gap.

The smoothness estimate consumes only the direction, gap, and feasible step interval. The active-state proof consumes only the weight representation. The global theorem later combines them with the pyramidal-width lemma.

### 5.4 Formalize good steps and drop counting separately

Do not encode “good step” as a complicated disjunction inside the main induction. Define a step result containing a progress certificate and a support-change certificate. A good-step result supplies (99.14). A drop-step result supplies a strict decrease of the finite support cardinality. A separate counting lemma uses:

- the initial support size is one;
- a toward step adds at most one atom;
- a drop step removes at least one atom;
- support size remains nonnegative.

This finite argument yields the lower bound on the number of good steps. Finally, prove the scalar iteration theorem

\[
h_{t+1}\le h_t \text{ on arbitrary steps},\qquad
h_{t+1}\le(1-\rho)h_t \text{ on good steps}
\]

implies \(h_t\le(1-\rho)^{k(t)}h_0\). The optimizer analysis then only has to supply the certificates. This organization makes the theorem robust to changes in the representation type or the precise oracle implementation.

A useful proof dependency diagram is:

~~~text
weight update algebra ──> active-set invariant ──> drop-step support decrease
oracle certificates ────> nonnegative gaps ──────> smooth one-step progress
pyramidal-width lemma ───────────────────────────> good-step contraction
             support counting + scalar recurrence
                              |
                              v
                    global linear convergence
~~~

## 6. Common failure modes

1. **Treating an away atom as a global oracle result.** It maximizes over the active set; the toward atom optimizes over the whole polytope.
2. **Using the wrong sign for the away gap.** With \(g=\nabla f(x)\), the nonnegative away gap is \(\langle g,v-x\rangle\), while the direction is \(x-v\).
3. **Allowing an arbitrary away step.** The bound in (99.9) is required to preserve nonnegative weights.
4. **Leaving zero-weight atoms active.** Drop steps are visible only when the active set is updated with the weights.
5. **Assuming a unique decomposition.** General polytopes can have redundant representations; the algorithm tracks one chosen representation.
6. **Applying the strong-convexity theorem to a linear example.** A simple linear example can illustrate a drop but cannot instantiate the theorem's \(\mu>0\) assumption.
7. **Claiming contraction at every iteration.** Drop steps may be truncated and are handled by counting, not by the good-step estimate.
8. **Replacing pyramidal width by minimum edge length.** They are different geometric quantities; use the established definition.
9. **Proving the rate before the support invariant.** The good-step count depends on precise finite-state bookkeeping.
10. **Hiding all inequalities in one tactic call.** Keep the oracle optimality, gap identity, smooth descent, weight nonnegativity, and recurrence as separate lemmas.

## 7. Exercises

1. Prove that \(g_t^{\mathrm{FW}}\ge0\) using only the convex representation of \(x_t\) and the LMO certificate.
2. Prove that \(g_t^{\mathrm A}\ge0\) using only the active-set maximizer certificate.
3. Starting from (99.8), prove that the updated weights sum to one.
4. Derive (99.9) from nonnegativity of the updated away weight.
5. Show that if \(0<\gamma\le\gamma_{\max}^{\mathrm A}\), each nonselected active weight remains positive.
6. For the simplex example in §3.1, verify the two gaps and the exact update to \(e_1\).
7. Derive the pairwise gap identity \(g_t^{\mathrm{FW}}+g_t^{\mathrm A}=\langle g_t,x_t-s_t\rangle+\langle g_t,v_t-x_t\rangle=\langle g_t,v_t-s_t\rangle\), and reconcile signs with the direction \(s_t-v_t\).
8. Use the descent lemma to prove decrease \(\langle r,d\rangle^2/(2L\|d\|^2)\) when the curvature-optimal step is feasible.
9. Explain why the choice of the larger of two gaps contributes a factor \(1/4\) after squaring in the rate.
10. Prove by induction that \(k\) good steps and arbitrary nonincreasing steps imply \(h\le(1-\rho)^k h_0\).
11. Formalize the away weight update over a finite vertex type and prove the weight-sum invariant.
12. State a drop-counting lemma for a run initialized at a vertex, identifying exactly which transitions can increase or decrease support.

## 8. Chapter summary

Away-step Frank–Wolfe augments the global linear oracle with an active-set maximizer. The toward direction adds a vertex; the away direction reduces the weight of a selected active vertex. Its maximum feasible step is determined by the current weight, and reaching that bound removes an atom from the active set.

For a smooth, strongly convex objective on a finite polytope with positive pyramidal width, a good AFW step contracts the objective gap by a fixed factor. Drop steps can be counted because each removes support and toward steps add at most one atom. In Lean, establish the weight invariants and support-counting lemmas independently from the oracle, smoothness, geometry, and scalar recurrence. This separation keeps finite algebra from obscuring the analytic convergence argument.

## Further reading

- Lacoste-Julien and Jaggi, [“On the Global Linear Convergence of Frank–Wolfe Optimization Variants”](https://proceedings.neurips.cc/paper_files/paper/2015/file/c058f544c737782deacefa532d9add4c-Paper.pdf), for the AFW algorithm, the pyramidal-width condition, and the good-step/drop-step rate.
- Chapter 98 — Frank–Wolfe and Projection-Free Optimization, for the standard method, curvature-based sublinear rates, and approximate linear oracles.
- Chapter 92 — Projected Gradient and Proximal Methods, for constrained first-order methods based on projection.

