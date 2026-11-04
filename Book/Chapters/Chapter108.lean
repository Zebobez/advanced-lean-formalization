module

public import Mathlib

public section

/-!
# Chapter 108 — Frank–Wolfe, Fenchel Duality, and Saddle-Point Certificates

Extracted from manuscript/chapters/part-23/chapter-108-frank-wolfe-fenchel-duality.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter108

-- Source Lean fence 1
def primalValue108 (w : ℚ) : ℚ := w ^ 2 / 2
def conjugateValue108 (α : ℚ) : ℚ := α ^ 2 / 2
def dualValue108 (α : ℚ) : ℚ := -conjugateValue108 α - |α|

def fenchelResidual108 (w α : ℚ) : ℚ :=
  primalValue108 w + conjugateValue108 α - α * w

def fwResidual108 (w α : ℚ) : ℚ := max (α * (w + 1)) (α * (w - 1))

theorem quadratic_weak_duality (w α : ℚ) :
    dualValue108 α ≤ primalValue108 w := by
  unfold dualValue108 conjugateValue108 primalValue108
  nlinarith [sq_nonneg w, sq_nonneg α, abs_nonneg α]

theorem fenchel_residual_nonnegative (w α : ℚ) :
    0 ≤ fenchelResidual108 w α := by
  unfold fenchelResidual108 primalValue108 conjugateValue108
  nlinarith [sq_nonneg (w - α)]

theorem fw_residual_nonnegative (w α : ℚ) (hw : -1 ≤ w) (hα : 0 ≤ α) :
    0 ≤ fwResidual108 w α := by
  have hfirst : 0 ≤ α * (w + 1) := mul_nonneg hα (by linarith)
  unfold fwResidual108
  exact le_trans hfirst (le_max_left _ _)

theorem primal_dual_gap_decomposition (w α : ℚ) (hα : 0 ≤ α) :
    primalValue108 w - dualValue108 α =
      fenchelResidual108 w α + fwResidual108 w α := by
  have hmax : α * (w - 1) ≤ α * (w + 1) := by nlinarith
  unfold primalValue108 dualValue108 conjugateValue108
    fenchelResidual108 fwResidual108
  rw [abs_of_nonneg hα, max_eq_left hmax]
  simp only [primalValue108, conjugateValue108]
  ring

theorem exact_quadratic_certificate_values :
    primalValue108 1 - dualValue108 1 = 2 ∧
    fenchelResidual108 1 1 = 0 ∧
    fwResidual108 1 1 = 2 := by
  norm_num [primalValue108, conjugateValue108, dualValue108,
    fenchelResidual108, fwResidual108]

theorem inexact_quadratic_certificate_values :
    primalValue108 1 - dualValue108 (1 / 2) = 9 / 8 ∧
    fenchelResidual108 1 (1 / 2) = 1 / 8 ∧
    fwResidual108 1 (1 / 2) = 1 := by
  norm_num [primalValue108, conjugateValue108, dualValue108,
    fenchelResidual108, fwResidual108]

end Book.Chapters.Chapter108
