module

public import Mathlib

public section

/-!
# Chapter 110 — ADMM, Augmented Lagrangians, and Residual Certificates

Extracted from manuscript/chapters/part-23/chapter-110-admm-and-augmented-lagrangians.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter110

-- Source Lean fence 1
def localUpdate110 (datum ρ z u : ℚ) : ℚ :=
  (datum + ρ * (z - u)) / (1 + ρ)

def consensusUpdate110 (xOne uOne xTwo uTwo : ℚ) : ℚ :=
  (xOne + uOne + xTwo + uTwo) / 2

def scaledDualUpdate110 (u x z : ℚ) : ℚ := u + x - z

def xOneFirst110 : ℚ := localUpdate110 0 1 0 0
def xTwoFirst110 : ℚ := localUpdate110 2 1 0 0
def zFirst110 : ℚ := consensusUpdate110 xOneFirst110 0 xTwoFirst110 0
def uOneFirst110 : ℚ := scaledDualUpdate110 0 xOneFirst110 zFirst110
def uTwoFirst110 : ℚ := scaledDualUpdate110 0 xTwoFirst110 zFirst110

def xOneSecond110 : ℚ := localUpdate110 0 1 zFirst110 uOneFirst110
def xTwoSecond110 : ℚ := localUpdate110 2 1 zFirst110 uTwoFirst110
def zSecond110 : ℚ :=
  consensusUpdate110 xOneSecond110 uOneFirst110 xTwoSecond110 uTwoFirst110
def uOneSecond110 : ℚ :=
  scaledDualUpdate110 uOneFirst110 xOneSecond110 zSecond110
def uTwoSecond110 : ℚ :=
  scaledDualUpdate110 uTwoFirst110 xTwoSecond110 zSecond110

theorem first_local_updates :
    xOneFirst110 = 0 ∧ xTwoFirst110 = 1 := by
  norm_num [xOneFirst110, xTwoFirst110, localUpdate110]

theorem first_consensus_and_dual_state :
    zFirst110 = 1 / 2 ∧ uOneFirst110 = -(1 : ℚ) / 2 ∧
      uTwoFirst110 = 1 / 2 := by
  norm_num [zFirst110, uOneFirst110, uTwoFirst110,
    xOneFirst110, xTwoFirst110, localUpdate110,
    consensusUpdate110, scaledDualUpdate110]

theorem second_local_updates :
    xOneSecond110 = 1 / 2 ∧ xTwoSecond110 = 1 := by
  norm_num [xOneSecond110, xTwoSecond110, zFirst110,
    uOneFirst110, uTwoFirst110, xOneFirst110, xTwoFirst110,
    localUpdate110, consensusUpdate110, scaledDualUpdate110]

theorem second_consensus_and_dual_state :
    zSecond110 = 3 / 4 ∧ uOneSecond110 = -(3 : ℚ) / 4 ∧
      uTwoSecond110 = 3 / 4 := by
  norm_num [zSecond110, uOneSecond110, uTwoSecond110,
    xOneSecond110, xTwoSecond110, zFirst110,
    uOneFirst110, uTwoFirst110, xOneFirst110, xTwoFirst110,
    localUpdate110, consensusUpdate110, scaledDualUpdate110]

theorem first_primal_residual :
    (xOneFirst110 - zFirst110, xTwoFirst110 - zFirst110) =
      (-(1 : ℚ) / 2, 1 / 2) := by
  norm_num [zFirst110, xOneFirst110, xTwoFirst110,
    localUpdate110, consensusUpdate110]

theorem second_primal_residual :
    (xOneSecond110 - zSecond110, xTwoSecond110 - zSecond110) =
      (-(1 : ℚ) / 4, 1 / 4) := by
  norm_num [zSecond110, xOneSecond110, xTwoSecond110,
    zFirst110, uOneFirst110, uTwoFirst110, xOneFirst110, xTwoFirst110,
    localUpdate110, consensusUpdate110, scaledDualUpdate110]

theorem consensus_solution_is_the_data_average :
    ((0 : ℚ) + 2) / 2 = 1 := by
  norm_num

end Book.Chapters.Chapter110
