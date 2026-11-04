module

public import Mathlib

public section

/-!
# Chapter 120 — Kurdyka–Łojasiewicz Convergence and Finite Length

Extracted from manuscript/chapters/part-23/chapter-120-kurdyka-lojasiewicz-convergence.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter120

-- Source Lean fence 1

open Filter
open scoped Topology

theorem finite_descent_budget
    (F q : ℕ → ℝ) (a lower : ℝ)
    (h_lower : ∀ n, lower ≤ F n)
    (h_step : ∀ n, F (n + 1) + a * q n ≤ F n)
    (N : ℕ) :
    a * ∑ n ∈ Finset.range N, q n ≤ F 0 - lower := by
  have htel : ∀ N, F N + a * ∑ n ∈ Finset.range N, q n ≤ F 0 := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        nlinarith [h_step N]
  have h := htel N
  have hl := h_lower N
  linarith

theorem kl_length_recurrence
    {sPrev sCurr scaledDrop : ℝ}
    (hPrev : 0 ≤ sPrev)
    (hDrop : 0 ≤ scaledDrop)
    (hProduct : sCurr ^ 2 ≤ sPrev * scaledDrop) :
    2 * sCurr ≤ sPrev + scaledDrop := by
  nlinarith [sq_nonneg (sPrev - scaledDrop)]

theorem finite_length_sequence_is_cauchy {X : Type*} [PseudoMetricSpace X]
    (x : ℕ → X)
    (h_length : Summable fun n => dist (x n) (x n.succ)) :
    CauchySeq x :=
  cauchySeq_of_summable_dist h_length

theorem finite_length_sequence_converges {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] (x : ℕ → X)
    (h_length : Summable fun n => dist (x n) (x n.succ)) :
    ∃ xLimit, Tendsto x atTop (𝓝 xLimit) :=
  cauchySeq_tendsto_of_complete (finite_length_sequence_is_cauchy x h_length)

end Book.Chapters.Chapter120
