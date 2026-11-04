module

public import Mathlib

public section

/-!
# Chapter 105 — Finite-Sum Frank–Wolfe: Variance Reduction and Gap Estimation

Extracted from manuscript/chapters/part-23/chapter-105-finite-sum-frank-wolfe.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter105

-- Source Lean fence 1
def componentGradientOne105 (x : ℝ) : ℝ := x - 1
def componentGradientTwo105 (x : ℝ) : ℝ := x + 1

noncomputable def fullGradient105 (x : ℝ) : ℝ :=
  (componentGradientOne105 x + componentGradientTwo105 x) / 2

noncomputable def svrgOne105 (x snapshot : ℝ) : ℝ :=
  componentGradientOne105 x - componentGradientOne105 snapshot + fullGradient105 snapshot

noncomputable def svrgTwo105 (x snapshot : ℝ) : ℝ :=
  componentGradientTwo105 x - componentGradientTwo105 snapshot + fullGradient105 snapshot

theorem full_gradient_at_snapshot_is_zero : fullGradient105 0 = 0 := by
  norm_num [fullGradient105, componentGradientOne105, componentGradientTwo105]

theorem full_gradient_at_current_point_is_one : fullGradient105 1 = 1 := by
  norm_num [fullGradient105, componentGradientOne105, componentGradientTwo105]

theorem svrg_sample_one_is_exact : svrgOne105 1 0 = fullGradient105 1 := by
  norm_num [svrgOne105, fullGradient105, componentGradientOne105,
    componentGradientTwo105]

theorem svrg_sample_two_is_exact : svrgTwo105 1 0 = fullGradient105 1 := by
  norm_num [svrgTwo105, fullGradient105, componentGradientOne105,
    componentGradientTwo105]

end Book.Chapters.Chapter105
