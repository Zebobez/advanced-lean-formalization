module

public import Mathlib

public section

/-!
# Chapter 109 — Primal–Dual Hybrid Gradient and Proximal Splitting

Extracted from manuscript/chapters/part-23/chapter-109-primal-dual-hybrid-gradient.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter109

-- Source Lean fence 1
def dualStep109 (σ y xBar b : ℚ) : ℚ :=
  (y + σ * xBar - σ * b) / (1 + σ)

def softThreshold109 (z threshold : ℚ) : ℚ :=
  if z < 0 then -max (-z - threshold) 0 else max (z - threshold) 0

def primalStep109 (τ penalty x y : ℚ) : ℚ :=
  softThreshold109 (x - τ * y) (τ * penalty)

def extrapolate109 (xNew xOld : ℚ) : ℚ := 2 * xNew - xOld

def firstDual109 : ℚ := dualStep109 (1 / 2) 0 0 2
def firstPrimal109 : ℚ := primalStep109 (1 / 2) (1 / 2) 0 firstDual109
def firstExtrapolate109 : ℚ := extrapolate109 firstPrimal109 0
def secondDual109 : ℚ := dualStep109 (1 / 2) firstDual109 firstExtrapolate109 2
def secondPrimal109 : ℚ :=
  primalStep109 (1 / 2) (1 / 2) firstPrimal109 secondDual109

theorem pdhg_step_size_condition :
    (1 : ℚ) / 2 * (1 / 2) * 1 ^ 2 < 1 := by
  norm_num

theorem first_dual_iterate : firstDual109 = -(2 : ℚ) / 3 := by
  norm_num [firstDual109, dualStep109]

theorem first_primal_iterate : firstPrimal109 = (1 : ℚ) / 12 := by
  norm_num [firstPrimal109, primalStep109, softThreshold109,
    firstDual109, dualStep109]

theorem first_extrapolated_iterate : firstExtrapolate109 = (1 : ℚ) / 6 := by
  norm_num [firstExtrapolate109, extrapolate109, firstPrimal109,
    primalStep109, softThreshold109, firstDual109, dualStep109]

theorem second_dual_iterate : secondDual109 = -(19 : ℚ) / 18 := by
  norm_num [secondDual109, dualStep109, firstExtrapolate109,
    extrapolate109, firstPrimal109, primalStep109, softThreshold109,
    firstDual109]

theorem second_primal_iterate : secondPrimal109 = (13 : ℚ) / 36 := by
  norm_num [secondPrimal109, primalStep109, softThreshold109,
    secondDual109, dualStep109, firstExtrapolate109, extrapolate109,
    firstPrimal109, firstDual109]

theorem lasso_solution_satisfies_kkt :
    (3 : ℚ) / 2 - 2 = -(1 : ℚ) / 2 ∧
    - (-(1 : ℚ) / 2) = (1 : ℚ) / 2 := by
  norm_num

end Book.Chapters.Chapter109
