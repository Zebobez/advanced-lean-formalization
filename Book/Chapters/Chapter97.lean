module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 97 — Adaptive Subgradients and AdaGrad

Extracted from manuscript/chapters/part-23/chapter-97-adaptive-subgradients-and-adagrad.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter97

-- Source Lean fence 1

open Book.Models.FiniteOptimization

def accumulatedSquares : Nat := 3 * 3 + 4 * 4

theorem adagrad_accumulator_example : accumulatedSquares = 25 := by decide

theorem accumulator_is_nonnegative : 0 ≤ accumulatedSquares := by omega

noncomputable def adagradScale97 {d : Nat} (delta : ℝ)
    (g : Nat → Fin d → ℝ) (t : Nat) (i : Fin d) : ℝ :=
  Real.sqrt (delta ^ 2 + ∑ s ∈ Finset.range t, (g s i) ^ 2)

theorem adagradScale97_pos {d : Nat} (delta : ℝ)
    (g : Nat → Fin d → ℝ) (t : Nat) (i : Fin d) (hδ : 0 < delta) :
    0 < adagradScale97 delta g t i := by
  unfold adagradScale97
  apply Real.sqrt_pos.2
  have hsum : 0 ≤ ∑ s ∈ Finset.range t, (g s i) ^ 2 := by
    apply Finset.sum_nonneg
    intro s hs
    exact sq_nonneg _
  have hδsq : 0 < delta ^ 2 := sq_pos_of_pos hδ
  nlinarith

theorem adagradScale97_succ_mono {d : Nat} (delta : ℝ)
    (g : Nat → Fin d → ℝ) (t : Nat) (i : Fin d) :
    adagradScale97 delta g t i ≤ adagradScale97 delta g (t + 1) i := by
  unfold adagradScale97
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_range_succ]
  nlinarith [sq_nonneg (g t i)]

end Book.Chapters.Chapter97
