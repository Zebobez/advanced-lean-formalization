module

public import Mathlib

public section

/-!
# Chapter 107 — Nonconvex Stationarity with Cached Frank–Wolfe Gradients

Extracted from manuscript/chapters/part-23/chapter-107-nonconvex-cached-frank-wolfe.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter107

-- Source Lean fence 1
noncomputable def quarticObjective107 : ℝ → ℝ :=
  ((fun x : ℝ => x ^ 2) - (fun _ : ℝ => (1 : ℝ) / 4)) ^ 2

theorem quartic_derivative_at_zero_is_zero :
    HasDerivAt quarticObjective107 0 0 := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ))
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ) / 4) 0 0 :=
    hasDerivAt_const (0 : ℝ) ((1 : ℝ) / 4)
  have hbase :
      HasDerivAt
        ((fun x : ℝ => x ^ 2) - (fun _ : ℝ => (1 : ℝ) / 4)) 0 0 := by
    simpa using hpow.sub hconst
  change HasDerivAt
    (((fun x : ℝ => x ^ 2) - (fun _ : ℝ => (1 : ℝ) / 4)) ^ 2) 0 0
  simpa using hbase.pow 2

theorem quartic_value_at_zero : quarticObjective107 0 = (1 : ℝ) / 16 := by
  norm_num [quarticObjective107]

theorem quartic_value_at_half : quarticObjective107 (1 / 2) = 0 := by
  norm_num [quarticObjective107]

theorem stationary_point_is_not_global_minimum :
    quarticObjective107 (1 / 2) < quarticObjective107 0 := by
  rw [quartic_value_at_half, quartic_value_at_zero]
  norm_num

theorem zero_gradient_gives_zero_fw_gap (s : ℝ) :
    (0 : ℝ) * (0 - s) = 0 := by
  ring

end Book.Chapters.Chapter107
