module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 93 — Estimate Sequences and Accelerated Gradient

Extracted from manuscript/chapters/part-23/chapter-93-estimate-sequences-and-accelerated-gradient.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter93

-- Source Lean fence 1

open Book.Models.FiniteOptimization

def estimateWeight (k : Nat) : Nat := (k + 1) * loss last

theorem estimate_sequence_vanishes_at_minimizer : ∀ k, estimateWeight k = 0 := by
  intro k
  simp [estimateWeight, loss, last]

noncomputable def acceleratedParameterStep93 (t : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * t ^ 2)) / 2

theorem acceleratedParameterStep93_identity (t : ℝ) :
    acceleratedParameterStep93 t ^ 2 - acceleratedParameterStep93 t = t ^ 2 := by
  have hsqrt : Real.sqrt (1 + 4 * t ^ 2) ^ 2 = 1 + 4 * t ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold acceleratedParameterStep93
  nlinarith [hsqrt]

theorem acceleratedParameterStep93_lower (t : ℝ) (ht : 0 ≤ t) :
    t + 1 / 2 ≤ acceleratedParameterStep93 t := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + 4 * t ^ 2) := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt (1 + 4 * t ^ 2) ^ 2 = 1 + 4 * t ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hroot : 2 * t ≤ Real.sqrt (1 + 4 * t ^ 2) := by
    apply (sq_le_sq₀ (by positivity) hsqrt_nonneg).1
    rw [hsqrt]
    nlinarith
  unfold acceleratedParameterStep93
  nlinarith

noncomputable def acceleratedParameter93 : Nat → ℝ
  | 0 => 1
  | n + 1 => acceleratedParameterStep93 (acceleratedParameter93 n)

theorem acceleratedParameter93_lower (n : Nat) :
    1 + (n : ℝ) / 2 ≤ acceleratedParameter93 n := by
  induction n with
  | zero => norm_num [acceleratedParameter93]
  | succ n ih =>
      have ht : 0 ≤ acceleratedParameter93 n := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hstep := acceleratedParameterStep93_lower (acceleratedParameter93 n) ht
      have hbound :
          1 + ((n : ℝ) + 1) / 2 ≤ acceleratedParameter93 n + 1 / 2 := by
        linarith
      have hnext :
          1 + ((n : ℝ) + 1) / 2 ≤ acceleratedParameterStep93 (acceleratedParameter93 n) :=
        le_trans hbound hstep
      simpa [acceleratedParameter93, Nat.cast_succ, add_div] using hnext

end Book.Chapters.Chapter93
