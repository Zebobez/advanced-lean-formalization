module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 99 — Away-Step Frank–Wolfe and Linear Convergence

Extracted from manuscript/chapters/part-23/chapter-99-away-step-frank-wolfe.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter99

-- Source Lean fence 1

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

end Book.Chapters.Chapter99
