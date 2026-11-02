module

public import Mathlib

public section

/-!
# Chapter 117 — Inexact Proximal Newton Methods and Forcing Terms

Extracted from manuscript/chapters/part-23/chapter-117-inexact-proximal-newton.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter117

-- Source Lean fence 2

theorem residual_slope_bound
    {slope step residual inner eta : ℝ}
    (hstep : 0 ≤ step)
    (hresidual : residual ≤ eta * step)
    (hcauchy : inner ≤ residual * step)
    (hslope : slope ≤ -(step ^ 2) + inner) :
    slope ≤ -(1 - eta) * step ^ 2 := by
  have hproduct : residual * step ≤ eta * step ^ 2 := by
    calc
      residual * step ≤ (eta * step) * step :=
        mul_le_mul_of_nonneg_right hresidual hstep
      _ = eta * step ^ 2 := by ring
  nlinarith

end Book.Chapters.Chapter117
