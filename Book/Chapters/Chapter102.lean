module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 102 — Frank–Wolfe over Strongly Convex Sets

Extracted from manuscript/chapters/part-23/chapter-102-frank-wolfe-strongly-convex-sets.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter102

-- Source Lean fence 1

open Book.Models.FiniteOptimization

def discreteCurvature : Int := Int.ofNat (loss first + loss last) - 2 * Int.ofNat (loss middle)

theorem discrete_curvature_is_positive : 0 < discreteCurvature := by decide

def ballObjective102 (x₁ x₂ : ℚ) : ℚ := ((x₁ - 3) ^ 2 + x₂ ^ 2) / 2

theorem unit_ball_first_coordinate_le_one {x₁ x₂ : ℚ}
    (hball : x₁ ^ 2 + x₂ ^ 2 ≤ 1) : x₁ ≤ 1 := by
  nlinarith [sq_nonneg (x₁ - 1), sq_nonneg x₂]

theorem unit_ball_oracle_certificate (s₁ s₂ : ℚ)
    (hs : s₁ ^ 2 + s₂ ^ 2 ≤ 1) :
    (-3 : ℚ) ≤ -3 * s₁ := by
  have hs₁ := unit_ball_first_coordinate_le_one hs
  nlinarith

theorem unit_ball_target_is_global_minimum (x₁ x₂ : ℚ)
    (hball : x₁ ^ 2 + x₂ ^ 2 ≤ 1) :
    ballObjective102 1 0 ≤ ballObjective102 x₁ x₂ := by
  have hx₁ := unit_ball_first_coordinate_le_one hball
  have hproduct : 0 ≤ (x₁ - 1) * (x₁ - 5) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  unfold ballObjective102
  nlinarith [hproduct, sq_nonneg x₂]

theorem unit_ball_line_search_clips_to_endpoint (eta : ℚ) (heta1 : eta ≤ 1) :
    ballObjective102 1 0 ≤ ballObjective102 eta 0 := by
  have hproduct : 0 ≤ (eta - 1) * (eta - 5) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  unfold ballObjective102
  nlinarith [hproduct]

end Book.Chapters.Chapter102
