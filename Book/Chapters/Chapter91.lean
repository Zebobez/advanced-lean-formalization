module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 91 — Smooth Convex Optimization and Gradient Descent

Extracted from manuscript/chapters/part-23/chapter-91-smooth-convex-optimization-and-gradient-descent.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter91

-- Source Lean fence 1

open Book.Models.FiniteOptimization

theorem gradient_step_decreases_from_first : loss (gradientStep first) < loss first := by decide

theorem gradient_step_reaches_minimum_from_middle : gradientStep middle = last := by decide

def scalarQuadratic91 (a x : ℚ) : ℚ := a * x ^ 2 / 2

def scalarGradientStep91 (a L x : ℚ) : ℚ := x - (a * x) / L

theorem scalarGradientStep91_factor (a L x : ℚ) :
    scalarGradientStep91 a L x = (1 - a / L) * x := by
  unfold scalarGradientStep91
  simp only [div_eq_mul_inv]
  ring

theorem scalarQuadratic91_step_identity (a L x : ℚ) :
    scalarQuadratic91 a (scalarGradientStep91 a L x) =
      (1 - a / L) ^ 2 * scalarQuadratic91 a x := by
  rw [scalarGradientStep91_factor]
  unfold scalarQuadratic91
  ring

theorem scalarQuadratic91_step_nonincreasing {a L x : ℚ}
    (ha : 0 ≤ a) (haL : a ≤ L) (hL : 0 < L) :
    scalarQuadratic91 a (scalarGradientStep91 a L x) ≤ scalarQuadratic91 a x := by
  rw [scalarQuadratic91_step_identity]
  have hratio_nonneg : 0 ≤ a / L := div_nonneg ha (le_of_lt hL)
  have hratio_le_one : a / L ≤ 1 := by
    rw [div_le_iff₀ hL]
    nlinarith
  have hfactor : (1 - a / L) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hratio_nonneg (show 0 ≤ 1 - a / L by linarith)]
  have hobjective : 0 ≤ scalarQuadratic91 a x := by
    unfold scalarQuadratic91
    positivity
  calc
    (1 - a / L) ^ 2 * scalarQuadratic91 a x ≤
        1 * scalarQuadratic91 a x := mul_le_mul_of_nonneg_right hfactor hobjective
    _ = scalarQuadratic91 a x := by ring

end Book.Chapters.Chapter91
