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

end Book.Chapters.Chapter120
