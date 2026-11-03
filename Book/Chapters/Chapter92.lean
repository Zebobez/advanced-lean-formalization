module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 92 — Projected Gradient and Proximal Methods

Extracted from manuscript/chapters/part-23/chapter-92-projected-gradient-and-proximal-methods.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter92

-- Source Lean fence 1

open Book.Models.FiniteOptimization

theorem projected_step_keeps_first_feasible : projectedStep first = first := by decide

theorem projected_step_reaches_minimum_from_middle : projectedStep middle = last := by decide

def IsProjectionCandidate {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (z p : E) : Prop :=
  p ∈ C ∧ ∀ y ∈ C, inner ℝ (z - p) (y - p) ≤ 0

theorem projection_candidate_is_nearest
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) {z p : E}
    (hp : IsProjectionCandidate C z p) :
    ‖z - p‖ = ⨅ y : C, ‖z - y‖ := by
  exact (norm_eq_iInf_iff_real_inner_le_zero hC hp.1).2 hp.2

theorem projection_candidate_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {z p q : E}
    (hp : IsProjectionCandidate C z p)
    (hq : IsProjectionCandidate C z q) :
    p = q := by
  have h₁ := hp.2 q hq.1
  have h₂ := hq.2 p hp.1
  have hidentity :
      inner ℝ (q - p) (q - p) =
        inner ℝ (z - p) (q - p) + inner ℝ (z - q) (p - q) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hinner : inner ℝ (q - p) (q - p) ≤ 0 := by
    rw [hidentity]
    exact add_nonpos h₁ h₂
  have hnorm_sq : ‖q - p‖ ^ 2 ≤ 0 := by
    rwa [← real_inner_self_eq_norm_sq]
  have hnorm_zero : ‖q - p‖ = 0 := by
    nlinarith [sq_nonneg (‖q - p‖)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)).symm

end Book.Chapters.Chapter92
