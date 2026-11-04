module

public import Book.Chapters.Chapter120
public import Mathlib

public section

/-!
# Chapter 121 — Fejér Monotonicity and Fixed-Point Convergence

Extracted from manuscript/chapters/part-24/chapter-121-fejer-monotonicity.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter121

-- Source Lean fence 1
open Filter
open scoped Topology

def QuasiNonexpansiveOn {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (S : Set X) : Prop :=
  ∀ x p, p ∈ S → dist (T x) p ≤ dist x p

-- Source Lean fence 2
theorem quasi_nonexpansive_update_is_fejer
    {X : Type*} [PseudoMetricSpace X]
    (x : ℕ → X) (T : X → X) (S : Set X)
    (hupdate : ∀ n, x (n + 1) = T (x n))
    (hT : QuasiNonexpansiveOn T S) :
    ∀ n p, p ∈ S → dist (x (n + 1)) p ≤ dist (x n) p := by
  intro n p hp
  rw [hupdate n]
  exact hT (x n) p hp

-- Source Lean fence 3
theorem quasi_nonexpansive_comp
    {X : Type*} [PseudoMetricSpace X]
    (T U : X → X) (S : Set X)
    (hT : QuasiNonexpansiveOn T S)
    (hU : QuasiNonexpansiveOn U S) :
    QuasiNonexpansiveOn (fun x => T (U x)) S := by
  intro x p hp
  exact (hT (U x) p hp).trans (hU x p hp)

-- Source Lean fence 4
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

-- Source Lean fence 5
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

-- Source Lean fence 6
def HasEscapingSubsequenceLimit {X : Type*} [TopologicalSpace X]
    (x : ℕ → X) (q : X) : Prop :=
  ∃ σ : ℕ → ℕ,
    Tendsto σ atTop atTop ∧
    Tendsto (fun k => x (σ k)) atTop (𝓝 q)

-- Source Lean fence 7
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

-- Source Lean fence 8
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

-- Source Lean fence 9
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

end Book.Chapters.Chapter121
