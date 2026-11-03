module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 100 — Fully Corrective Frank–Wolfe and Active-Set Optimization

Extracted from manuscript/chapters/part-23/chapter-100-fully-corrective-frank-wolfe.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter100

-- Source Lean fence 1

open Book.Models.FiniteOptimization

def correctedWeights : Candidate → Nat := fun x => if x = last then 1 else 0
def totalCorrectedWeight : Nat :=
  correctedWeights first + correctedWeights middle + correctedWeights last

theorem fully_corrective_weights_are_normalized : totalCorrectedWeight = 1 := by decide

theorem fully_corrective_support_contains_minimizer : correctedWeights last = 1 := by decide

def edgeObjective100 (alpha : ℚ) : ℚ :=
  ((alpha - 1 / 5) ^ 2 + (1 / 2 - alpha) ^ 2 + (3 / 10) ^ 2) / 2

theorem first_correction_edge_minimizes (alpha : ℚ) :
    edgeObjective100 (7 / 20) ≤ edgeObjective100 alpha := by
  unfold edgeObjective100
  nlinarith [sq_nonneg (alpha - 7 / 20)]

theorem first_correction_edge_objective : edgeObjective100 (7 / 20) = 27 / 400 := by
  norm_num [edgeObjective100]

def simplexQuadratic100 (x₁ x₂ x₃ : ℚ) : ℚ :=
  ((x₁ - 1 / 5) ^ 2 + (x₂ - 1 / 2) ^ 2 + (x₃ - 3 / 10) ^ 2) / 2

theorem simplex_target_objective_zero :
    simplexQuadratic100 (1 / 5) (1 / 2) (3 / 10) = 0 := by
  norm_num [simplexQuadratic100]

theorem simplex_target_is_global_minimum (x₁ x₂ x₃ : ℚ) :
    simplexQuadratic100 (1 / 5) (1 / 2) (3 / 10) ≤ simplexQuadratic100 x₁ x₂ x₃ := by
  rw [simplex_target_objective_zero]
  unfold simplexQuadratic100
  positivity

end Book.Chapters.Chapter100
