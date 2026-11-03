module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 101 — Pairwise Frank–Wolfe and Sparse Support Transfers

Extracted from manuscript/chapters/part-23/chapter-101-pairwise-frank-wolfe.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter101

-- Source Lean fence 1

open Book.Models.FiniteOptimization

theorem pairwise_update_conserves_mass :
    pairMass (transferOne 2 1).1 (transferOne 2 1).2 = pairMass 2 1 := by decide

theorem pairwise_update_stays_nonnegative : (transferOne 2 1).1 ≥ 0 := by decide

def pairwiseTransfer101 (weights : Fin 3 → ℚ) (away toward : Fin 3)
    (gamma : ℚ) (i : Fin 3) : ℚ :=
  if i = away then weights i - gamma
  else if i = toward then weights i + gamma
  else weights i

def dropWeights101 : Fin 3 → ℚ := fun i =>
  if i = 0 then 11 / 20 else if i = 1 then 7 / 20 else 1 / 10

theorem pairwise_drop_update_exact :
    pairwiseTransfer101 dropWeights101 2 0 (1 / 10) =
      fun i => if i = 0 then 13 / 20 else if i = 1 then 7 / 20 else 0 := by
  funext i
  fin_cases i <;> norm_num [pairwiseTransfer101, dropWeights101]

theorem pairwise_drop_preserves_mass :
    (∑ i : Fin 3, pairwiseTransfer101 dropWeights101 2 0 (1 / 10) i) = 1 := by
  norm_num [Fin.sum_univ_succ, pairwiseTransfer101, dropWeights101]

theorem pairwise_drop_removes_away_atom :
    pairwiseTransfer101 dropWeights101 2 0 (1 / 10) 2 = 0 := by
  norm_num [pairwiseTransfer101, dropWeights101]

def swapWeights101 : Fin 3 → ℚ := fun i =>
  if i = 0 then 1 / 5 else if i = 1 then 4 / 5 else 0

theorem pairwise_swap_update_exact :
    pairwiseTransfer101 swapWeights101 1 2 (4 / 5) =
      fun i => if i = 0 then 1 / 5 else if i = 1 then 0 else 4 / 5 := by
  funext i
  fin_cases i <;> norm_num [pairwiseTransfer101, swapWeights101]

theorem pairwise_swap_preserves_mass :
    (∑ i : Fin 3, pairwiseTransfer101 swapWeights101 1 2 (4 / 5) i) = 1 := by
  norm_num [Fin.sum_univ_succ, pairwiseTransfer101, swapWeights101]

theorem pairwise_swap_replaces_away_atom :
    pairwiseTransfer101 swapWeights101 1 2 (4 / 5) 1 = 0 ∧
      0 < pairwiseTransfer101 swapWeights101 1 2 (4 / 5) 2 := by
  norm_num [pairwiseTransfer101, swapWeights101]

end Book.Chapters.Chapter101
