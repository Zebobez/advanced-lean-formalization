module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 43 — Conditional Independence

Extracted from manuscript/chapters/part-06/chapter-43-conditional-independence.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter43

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def independentJoint : Kernel := resetKernel

theorem everyIndependentCellHasUnitWeight : independentJoint zero zero = 1 := by decide
theorem secondIndependentCellHasUnitWeight : independentJoint one zero = 1 := by decide

-- Source Lean fence 2
theorem exercise_43_1_hidden_row_zero_factors :
    (1 / 10 : ℚ) * (1 / 10) = 1 / 100 := by
  norm_num

theorem exercise_43_2_hidden_row_one_factors :
    (9 / 10 : ℚ) * (9 / 10) = 81 / 100 := by
  norm_num

theorem exercise_43_3_hidden_marginal_success :
    (1 / 2 : ℚ) * (1 / 10) + (1 / 2) * (9 / 10) = 1 / 2 := by
  norm_num

theorem exercise_43_4_hidden_joint_success :
    (1 / 2 : ℚ) * (1 / 10) * (1 / 10) +
        (1 / 2) * (9 / 10) * (9 / 10) = 41 / 100 := by
  norm_num

theorem exercise_43_5_hidden_variables_not_independent :
    (41 / 100 : ℚ) ≠ (1 / 2) * (1 / 2) := by
  norm_num

-- Source Lean fence 3
def bernoulliAtom (p : ℚ) (x : Bool) : ℚ := if x then p else 1 - p

def hiddenSuccessProb (θ : Bool) : ℚ := if θ then 9 / 10 else 1 / 10

def hiddenJointAtom (θ x y : Bool) : ℚ :=
  bernoulliAtom (hiddenSuccessProb θ) x * bernoulliAtom (hiddenSuccessProb θ) y

def hiddenXMarginal (θ x : Bool) : ℚ := ∑ y : Bool, hiddenJointAtom θ x y

def hiddenYMarginal (θ y : Bool) : ℚ := ∑ x : Bool, hiddenJointAtom θ x y

theorem bernoulliAtom_total (p : ℚ) : ∑ x : Bool, bernoulliAtom p x = 1 := by
  simp [bernoulliAtom]

theorem hiddenXMarginal_eq (θ x : Bool) :
    hiddenXMarginal θ x = bernoulliAtom (hiddenSuccessProb θ) x := by
  unfold hiddenXMarginal hiddenJointAtom
  rw [← Finset.mul_sum, bernoulliAtom_total]
  ring

theorem hiddenYMarginal_eq (θ y : Bool) :
    hiddenYMarginal θ y = bernoulliAtom (hiddenSuccessProb θ) y := by
  unfold hiddenYMarginal hiddenJointAtom
  rw [← Finset.sum_mul, bernoulliAtom_total]
  ring

theorem hiddenJoint_conditional_independence (θ x y : Bool) :
    hiddenJointAtom θ x y = hiddenXMarginal θ x * hiddenYMarginal θ y := by
  rw [hiddenXMarginal_eq, hiddenYMarginal_eq, hiddenJointAtom]

end Book.Chapters.Chapter43
