# Chapter 121 — Fejér Monotonicity and Fixed-Point Convergence

> **Audience.** This chapter follows the descent and finite-length arguments of Chapters 91–120. It develops a complementary convergence method for fixed-point and feasibility algorithms, especially when one has a family of solutions but no convenient scalar objective whose values decrease.

Many algorithms in optimization and fixed-point theory move toward a set of solutions without minimizing a single explicit energy at every step. Alternating projections, averaged operator iterations, and splitting methods often provide a different certificate: every solution remains at least as close to the next iterate as it was to the current one. This is **Fejér monotonicity**.

Fejér monotonicity is powerful because it controls an entire orbit relative to every solution at once. It is also easy to overread. It proves convergence of the distances to each solution; it does not, by itself, prove that the iterates have a cluster point, that a cluster point is a solution, or that the full sequence converges. This chapter isolates those logical steps and formalizes the metric core in Lean.

## Learning objectives

After this chapter, you should be able to:

- state Fejér monotonicity for a sequence and a nonempty target set;
- derive Fejér monotonicity from a quasi-nonexpansive update;
- prove that the distances to each target point converge;
- compare cluster points by identifying their limiting distances;
- separate distance control, asymptotic regularity, and solution identification;
- recognize when compactness, closedness, or weak-topology hypotheses supply missing steps;
- formalize the metric sequence arguments without encoding a particular algorithm prematurely.

## 121.1 — The distance profile of an iterate sequence

Let \((X,d)\) be a metric space, let \(S\subseteq X\) be a set of solutions, and let \((x_n)_{n\ge 0}\) be an iterate sequence. The sequence is **Fejér monotone with respect to \(S\)** when
\[
  d(x_{n+1},p)\le d(x_n,p)
  \qquad(n\ge 0,\ p\in S).
  \tag{121.1}
\]
The quantifier over every \(p\in S\) is essential. A method may reduce its distance to one selected solution while moving farther from another. The Fejér condition says that the whole distance profile on the solution set is nonincreasing.

For a fixed \(p\in S\), the scalar sequence \(n\mapsto d(x_n,p)\) is nonnegative and nonincreasing. Consequently, it converges to its infimum. In particular, for any two indices \(m\le n\),
\[
  d(x_n,p)\le d(x_m,p)\le d(x_0,p).
  \tag{121.2}
\]
If \(S\) is nonempty, choose one \(p\in S\). The triangle inequality and (121.2) show that the orbit is bounded:
\[
  d(x_n,x_0)\le d(x_n,p)+d(p,x_0)\le 2d(x_0,p).
\]
The bound depends on a chosen solution, but boundedness does not require that we know the solution explicitly in a computation. In a theorem, it is enough to supply a witness that \(S\) is nonempty.

The Lean development below uses a predicate for a map that does not increase distances to points in a designated set. Such a map is often called **quasi-nonexpansive on \(S\)**. The definition is deliberately relative to \(S\); it makes no claim about distances between two arbitrary inputs.

```lean
open Filter
open scoped Topology

def QuasiNonexpansiveOn {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (S : Set X) : Prop :=
  ∀ x p, p ∈ S → dist (T x) p ≤ dist x p
```

The metric class is initially only a pseudometric space because distance inequalities and limits do not need point separation. We will add a `MetricSpace` assumption only when converting distance zero into equality of points.

## 121.2 — From an update rule to Fejér monotonicity

Suppose the algorithm applies a single map at each iteration:
\[
  x_{n+1}=T(x_n).
  \tag{121.3}
\]
If \(T\) is quasi-nonexpansive on \(S\), then substituting (121.3) into its defining inequality gives (121.1) immediately. This small theorem is useful because the algorithm-specific proof can focus on the map property, while later convergence lemmas consume only the Fejér inequality.

```lean
theorem quasi_nonexpansive_update_is_fejer
    {X : Type*} [PseudoMetricSpace X]
    (x : ℕ → X) (T : X → X) (S : Set X)
    (hupdate : ∀ n, x (n + 1) = T (x n))
    (hT : QuasiNonexpansiveOn T S) :
    ∀ n p, p ∈ S → dist (x (n + 1)) p ≤ dist (x n) p := by
  intro n p hp
  rw [hupdate n]
  exact hT (x n) p hp
```

Quasi-nonexpansiveness is preserved under composition when each map has the same target set. The proof is a two-line transitivity argument, but the statement captures a useful design pattern for splitting algorithms whose update is assembled from several operators.

```lean
theorem quasi_nonexpansive_comp
    {X : Type*} [PseudoMetricSpace X]
    (T U : X → X) (S : Set X)
    (hT : QuasiNonexpansiveOn T S)
    (hU : QuasiNonexpansiveOn U S) :
    QuasiNonexpansiveOn (fun x => T (U x)) S := by
  intro x p hp
  exact (hT (U x) p hp).trans (hU x p hp)
```

There is a useful refinement for firmly nonexpansive maps in a Hilbert space. If \(p\) is a fixed point, firm nonexpansiveness gives a **Pythagorean decrease** of the form
\[
  \|T x-p\|^2+\|x-Tx\|^2\le \|x-p\|^2.
  \tag{121.4}
\]
Dropping the nonnegative residual term yields quasi-nonexpansiveness. Keeping that term and summing over \(n\) yields a finite-energy estimate for the fixed-point residuals \(\|x_n-Tx_n\|^2\). Thus one inequality can provide both Fejér monotonicity and asymptotic regularity, but those are distinct consequences and should have distinct theorem statements.

The following elementary lemma translates a squared-distance descent estimate into the unsquared Fejér inequality. It is useful when an algorithm naturally produces (121.4). The residual in the next theorem is an arbitrary real-valued certificate; it need not be identified with a particular operator residual at this abstraction layer.

```lean
theorem nonnegative_le_of_sq_le_sq {a b : ℝ}
    (ha : 0 ≤ a) (_hb : 0 ≤ b) (h : b ^ 2 ≤ a ^ 2) :
    b ≤ a := by
  nlinarith [ha, _hb, h]

theorem squared_descent_implies_fejer
    {X : Type*} [PseudoMetricSpace X]
    (x : ℕ → X) (S : Set X) (residual : ℕ → X → ℝ)
    (hdescent : ∀ n p, p ∈ S →
      dist (x (n + 1)) p ^ 2 + residual n p ^ 2 ≤ dist (x n) p ^ 2) :
    ∀ n p, p ∈ S → dist (x (n + 1)) p ≤ dist (x n) p := by
  intro n p hp
  apply nonnegative_le_of_sq_le_sq (dist_nonneg) (dist_nonneg)
  nlinarith [hdescent n p hp, sq_nonneg (residual n p)]
```

The distinction between \(\sum r_n^2<\infty\) and \(\sum r_n<\infty\) matters here. A square-residual estimate often implies \(r_n\to0\), hence asymptotic regularity, but it need not imply finite path length. Chapter 120 used a stronger KL recurrence to obtain summability of step lengths. Fejér analysis usually follows a different route: it combines distance limits with compactness or a property of the ambient topology to identify the orbit's limit.

## 121.3 — Convergence of the distance to a solution

For fixed \(p\in S\), set \(a_n=d(x_n,p)\). By (121.1), \((a_n)\) is antitone, and by nonnegativity its range is bounded below by zero. The monotone convergence theorem for real-valued sequences therefore gives
\[
  d(x_n,p)\longrightarrow \inf_{m\ge0}d(x_m,p).
  \tag{121.5}
\]
In Lean, `tendsto_atTop_ciInf` states precisely this order-theoretic limit. Keeping the infimum in the conclusion is more informative than introducing an unspecified real constant: subsequent subsequence arguments can compare against the same canonical value.

```lean
theorem fejer_distances_converge
    {X : Type*} [PseudoMetricSpace X]
    (x : ℕ → X) (S : Set X) (p : X) (hp : p ∈ S)
    (hfejer : ∀ n q, q ∈ S →
      dist (x (n + 1)) q ≤ dist (x n) q) :
    Tendsto (fun n => dist (x n) p) atTop
      (𝓝 (⨅ n, dist (x n) p)) := by
  have hanti : Antitone (fun n => dist (x n) p) := by
    intro m n hmn
    induction hmn with
    | refl => rfl
    | @step n hmn ih =>
        exact (hfejer n p hp).trans ih
  have hbound : BddBelow (Set.range fun n => dist (x n) p) := by
    refine ⟨0, ?_⟩
    intro d hd
    rcases hd with ⟨n, rfl⟩
    exact dist_nonneg
  exact tendsto_atTop_ciInf hanti hbound
```

Notice what is absent from this theorem: it does not use completeness, boundedness of the whole space, or continuity of an update map. These assumptions are unnecessary for the scalar distance limit. Good formalization keeps such hypotheses out of statements that do not need them.

## 121.4 — A subsequential limit inherits the distance limit

To compare two candidate cluster points, we need to know that the distance from a candidate to a fixed solution is the same limiting distance as in (121.5). A subsequence whose indices escape to infinity inherits every ordinary sequence limit. The following predicate records only those two facts: an index map tends to infinity, and the corresponding selected iterates converge to a point.

```lean
def HasEscapingSubsequenceLimit {X : Type*} [TopologicalSpace X]
    (x : ℕ → X) (q : X) : Prop :=
  ∃ σ : ℕ → ℕ,
    Tendsto σ atTop atTop ∧
    Tendsto (fun k => x (σ k)) atTop (𝓝 q)
```

Any strictly increasing subsequence index map is an example of an escaping map. We use the more general form because the proof only needs \(\sigma(k)\to\infty\), not strict monotonicity. The distance function is continuous in either argument on a pseudometric space, so if \(x_{\sigma(k)}\to q\), then \(d(x_{\sigma(k)},p)\to d(q,p)\). On the other hand, composing (121.5) with the escaping map shows that the same scalar sequence tends to the infimum. Uniqueness of limits in \(\mathbb R\) identifies them.

```lean
theorem fejer_subsequence_distance_eq
    {X : Type*} [PseudoMetricSpace X]
    (x : ℕ → X) (S : Set X) (p q : X)
    (hp : p ∈ S)
    (hfejer : ∀ n r, r ∈ S →
      dist (x (n + 1)) r ≤ dist (x n) r)
    (hq : HasEscapingSubsequenceLimit x q) :
    dist q p = ⨅ n, dist (x n) p := by
  obtain ⟨σ, hσ, hq⟩ := hq
  have hdist := fejer_distances_converge x S p hp hfejer
  have hviaFejer := hdist.comp hσ
  have hviaLimit :
      Tendsto (fun k => dist (x (σ k)) p) atTop (𝓝 (dist q p)) :=
    hq.dist tendsto_const_nhds
  exact tendsto_nhds_unique hviaLimit hviaFejer
```

This lemma is the main interface between order and topology. It does not say that \(q\in S\). It says that every escaping subsequential limit has the same distance to each fixed \(p\in S\) as the entire distance profile. Membership of the limit in the solution set must come from a separate closedness or residual argument.

## 121.5 — Uniqueness of cluster points and full convergence

Assume now that \(X\) is a metric space and that \(p\in S\) is itself a cluster point. Applying the preceding lemma with \(q=p\) shows that the infimum in (121.5) is zero. Applying it again to any other cluster point \(q\) gives \(d(q,p)=0\), so metric separation forces \(q=p\).

```lean
theorem fejer_cluster_point_unique
    {X : Type*} [MetricSpace X]
    (x : ℕ → X) (S : Set X) (p q : X)
    (hp : p ∈ S)
    (hfejer : ∀ n r, r ∈ S →
      dist (x (n + 1)) r ≤ dist (x n) r)
    (hpCluster : HasEscapingSubsequenceLimit x p)
    (hqCluster : HasEscapingSubsequenceLimit x q) :
    q = p := by
  have hpInf := fejer_subsequence_distance_eq x S p p hp hfejer hpCluster
  have hqInf := fejer_subsequence_distance_eq x S p q hp hfejer hqCluster
  have hInfZero : (⨅ n, dist (x n) p) = 0 := by
    simpa using hpInf.symm
  rw [hInfZero] at hqInf
  exact dist_eq_zero.mp hqInf
```

This theorem gives a standard convergence strategy in finite-dimensional spaces. First, Fejér monotonicity bounds the orbit. Next, compactness of a closed bounded region supplies a convergent subsequence. If the algorithm's residuals or update relation show every cluster point belongs to \(S\), then the theorem above shows that there can be at most one cluster point. Finally, boundedness plus uniqueness of cluster points implies convergence of the full sequence. The last step is a compactness argument: if the sequence did not converge to its unique cluster point, some subsequence would stay a fixed positive distance away, and compactness would give that subsequence a different cluster point.

For an infinite-dimensional Hilbert space, bounded sets need not be compact in the norm topology. Weak compactness can supply weakly convergent subsequences in reflexive settings, but the metric argument above cannot simply be reused with weak convergence: the norm-distance function is not generally continuous in the weak topology. Weak-convergence theorems therefore add structure such as Opial's condition and a demiclosedness principle. These are substantive hypotheses, not Lean automation details. This chapter formalizes the strong-metric cluster-point argument and leaves weak-topology variants for a later treatment.

## 121.6 — Examples: projections and averaged iterations

Let \(C\) be a nonempty closed convex subset of a Hilbert space, and let \(P_C\) denote its metric projection. For any \(p\in C\), the projection inequality gives
\[
  \|P_Cx-p\|^2+\|x-P_Cx\|^2\le \|x-p\|^2.
  \tag{121.6}
\]
Thus one projection step is Fejér monotone with respect to \(C\). Repeatedly applying the same projection is not an interesting algorithm—it reaches the set after one step—but (121.6) becomes useful when each iteration applies a different projection from a family \((P_{C_n})\) and the target is the common intersection. Every individual set contains every common solution, so each projection step preserves the Fejér inequality with respect to the intersection.

If \(T\) is nonexpansive and has a fixed point \(p\), then
\[
  d(Tx,p)=d(Tx,Tp)\le d(x,p).
\]
Therefore the Picard iteration \(x_{n+1}=T x_n\) is Fejér monotone with respect to the fixed-point set. For the relaxed iteration
\[
  x_{n+1}=(1-\lambda_n)x_n+\lambda_n T x_n,
  \qquad 0\le\lambda_n\le1,
  \tag{121.7}
\]
convexity of the norm yields
\[
  \|x_{n+1}-p\|
  \le (1-\lambda_n)\|x_n-p\|+\lambda_n\|T x_n-p\|
  \le \|x_n-p\|.
\]
The pointwise Fejér proof is simple once the ambient convex structure and the parameter bounds are exposed. Formalizing the setup as an affine space and a convex combination is more reusable than hard-coding vectors as finite tuples.

The following theorem records a different but related limit principle. If an iteration converges in a topology and the graph of its update map is closed, then its limit is a fixed point. This conclusion does not require Fejér monotonicity; it is the closed-graph limit step used after convergence has been established by some other method. It reuses Chapter 120's general relation theorem.

```lean
theorem closed_graph_iteration_limit
    {X : Type*} [TopologicalSpace X]
    (T : X → X)
    (hclosed : IsClosed {p : X × X | T p.1 = p.2})
    (x : ℕ → X) (xLimit : X)
    (hx : Tendsto x atTop (𝓝 xLimit))
    (hupdate : ∀ n, T (x n) = x (n + 1)) :
    T xLimit = xLimit := by
  have hxnext : Tendsto (fun n => x (n + 1)) atTop (𝓝 xLimit) :=
    hx.comp (tendsto_add_atTop_nat 1)
  exact Book.Chapters.Chapter120.closed_relation_limit
    (fun y z => T y = z) hclosed x (fun n => x (n + 1))
    xLimit xLimit hx hxnext hupdate
```

The closed-graph hypothesis is sufficient for this exact fixed-point graph relation. If the update map is discontinuous, closedness still matters and continuity cannot be silently assumed. Conversely, when \(T\) is continuous, its graph is closed whenever the codomain is Hausdorff; in a metric codomain that separation condition is automatic.

## 121.7 — What the Fejér estimate does not prove

The proof architecture can be summarized as follows:

```text
algorithmic inequality
        ↓
nonincreasing distances to every solution
        ↓
one limiting distance for each solution
        ↓
cluster-point comparison
        ↓
convergence, once cluster-point existence and solution membership are supplied
```

Each arrow has an assumption behind it. The first arrow is the algorithm's burden: prove quasi-nonexpansiveness, firm nonexpansiveness, or another estimate that implies (121.1). The second arrow is the monotone convergence theorem. The third arrow uses continuity of the distance in a metric topology. The last arrow requires compactness or a substitute to obtain cluster points, plus a closedness, residual, or demiclosedness theorem to place them in the solution set.

There are useful approximate versions. If the inequality is perturbed to
\[
  d(x_{n+1},p)\le d(x_n,p)+\varepsilon_n
  \qquad(p\in S),
  \tag{121.8}
\]
with \(\varepsilon_n\ge0\) and \(\sum_n\varepsilon_n<\infty\), the sequence is called quasi-Fejér monotone. One can compensate the accumulated future error by considering
\[
  d(x_n,p)+\sum_{k=n}^{\infty}\varepsilon_k,
\]
which is nonincreasing. This reduces many perturbed arguments to the monotone-distance case, but it adds a summability interface. A robust library can state the exact Fejér result first, then prove quasi-Fejér variants by applying it to the corrected distance sequence.

## 121.8 — Lean design and reusable interfaces

The module illustrates several proof-engineering choices.

1. **State the weakest topology needed.** Distance convergence uses only a pseudometric. Equality of cluster points requires metric separation. No completeness hypothesis belongs in either theorem.
2. **Separate algorithm properties from sequence consequences.** `QuasiNonexpansiveOn` describes the map, while `quasi_nonexpansive_update_is_fejer` translates an update rule into a sequence inequality.
3. **Keep the infimum visible.** The limit in `fejer_distances_converge` is the infimum of the full distance profile. This makes the cluster-point argument a comparison of two explicit limits.
4. **Represent subsequences by their mathematical obligations.** `HasEscapingSubsequenceLimit` asks for convergence of indices to infinity and convergence of the selected iterates. It avoids committing the central lemma to one particular subsequence API.
5. **Do not conflate asymptotic regularity and convergence.** A residual tending to zero says successive updates become small. The orbit may still drift over an unbounded time horizon unless additional distance, compactness, or summability information rules that out.
6. **Treat closedness as a named premise.** The fixed-point limit theorem reuses the general closed-relation theorem instead of unfolding topology in each application.

In a larger formalization, a structure for an iterative method could package a carrier set, an update map, a solution set, and a proof that the update is quasi-nonexpansive on that solution set. A second structure could carry compactness or weak compactness data. Keeping these interfaces separate allows the metric theory to be reused by projection, splitting, and fixed-point algorithms without importing their analytic details into every sequence lemma.

## Exercises

1. Show that a nonexpansive self-map is quasi-nonexpansive on its fixed-point set.
2. Formalize the boundedness of a Fejér-monotone orbit given a witness \(p\in S\).
3. Prove that a strictly increasing map \(\sigma:\mathbb N\to\mathbb N\) tends to infinity, and use it to derive the escaping-subsequence condition.
4. Suppose the squared descent estimate (121.4) holds at every step. Telescope it to prove that the squared residuals form a summable sequence.
5. Deduce from the previous exercise that the residuals tend to zero, and state clearly why this alone does not imply convergence of \((x_n)\).
6. Prove that the metric projection onto a nonempty closed convex set is quasi-nonexpansive on that set.
7. Give an example of a bounded sequence with two cluster points that is not Fejér monotone with respect to either singleton target set.
8. Complete the compactness argument showing that a sequence in a compact metric space with exactly one cluster point converges to it.
9. Derive the quasi-Fejér correction after (121.8), carefully managing the index shift in the error tail.
10. Identify which theorem in an alternating-projection development proves that every cluster point belongs to the intersection, and whether the proof uses strong or weak convergence.
11. Explain why weak convergence of \(x_n\) does not generally imply convergence of \(\|x_n-p\|\), even though weakly convergent sequences are bounded in a Hilbert space.
12. Instantiate `closed_graph_iteration_limit` with a continuous map on a metric space and derive the required closed-graph hypothesis.

## Chapter summary

Fejér monotonicity turns an algorithmic distance estimate into a convergent scalar profile for every solution point. A quasi-nonexpansive update supplies the basic inequality, while stronger squared estimates can also control residual energy. The common distance limits force cluster points to agree when one cluster point lies in the solution set and the ambient space separates points.

This is a convergence framework with explicit interfaces. Fejér monotonicity gives distance convergence and boundedness relative to any chosen solution. It does not create cluster points or prove that they solve the problem. Those conclusions need compactness or weak compactness and an appropriate closedness or demiclosedness argument. In Lean, representing those proof obligations separately keeps the core sequence lemmas short and reusable.

## Further reading

- Z. Opial, [“Weak convergence of the sequence of successive approximations for nonexpansive mappings”](https://doi.org/10.1090/S0002-9904-1967-11761-0), *Bulletin of the American Mathematical Society* 73 (1967), 591–597, for a classical weak-convergence theorem and the role of Opial's condition.
- P. L. Combettes, [“Quasi-Fejérian analysis of some optimization algorithms”](https://pcombet.math.ncsu.edu/livre1.pdf), for a systematic treatment of quasi-Fejér sequences and optimization methods.
- Chapter 120 proves full convergence by a finite-length argument. This chapter gives a complementary route based on distance profiles, cluster points, and fixed-point structure.
