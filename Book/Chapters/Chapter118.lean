module

public import Mathlib

public section

/-!
# Chapter 118 — Global Convergence of Proximal Newton Iterations

Extracted from manuscript/chapters/part-23/chapter-118-global-convergence-proximal-newton.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter118

-- Source Lean fence 1

theorem finite_energy_bound
    (F q : ℕ → ℝ) (c lower : ℝ)
    (h_lower : ∀ n, lower ≤ F n)
    (h_step : ∀ n, F (n + 1) ≤ F n - c * q n)
    (N : ℕ) :
    c * (∑ n ∈ Finset.range N, q n) ≤ F 0 - lower := by
  have htel : ∀ N, F N ≤ F 0 - c * (∑ n ∈ Finset.range N, q n) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        nlinarith [ih, h_step N]
  nlinarith [htel N, h_lower N]

end Book.Chapters.Chapter118
