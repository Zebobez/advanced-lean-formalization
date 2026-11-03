module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 59 — Feynman–Kac Semigroups and Killing

Extracted from manuscript/chapters/part-12/chapter-59-feynman-kac-semigroups-and-killing.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter59

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def killingPotential : State → Nat := fun _ => 1
def killedFlipWeight (i j : State) : Nat := killingPotential i * flipKernel i j

theorem constantKillingLeavesTheOffDiagonalWeight : killedFlipWeight zero one = 2 := by decide

-- Source Lean fence 2
def killedTwoStateGenerator (a b v : ℚ) (i j : State) : ℚ :=
  if i = zero then (if j = zero then -a else a)
  else if j = zero then b else -(b + v)

def killedTwoStateRowSum (a b v : ℚ) (i : State) : ℚ :=
  killedTwoStateGenerator a b v i zero + killedTwoStateGenerator a b v i one

theorem killed_two_state_row_sums (a b v : ℚ) :
    killedTwoStateRowSum a b v zero = 0 ∧
      killedTwoStateRowSum a b v one = -v := by
  constructor
  · simp [killedTwoStateRowSum, killedTwoStateGenerator, zero, one]
  · simp [killedTwoStateRowSum, killedTwoStateGenerator, zero, one]

-- Source Lean fence 3
def augmentedKillingGenerator (a b v : ℚ) (i j : Fin 3) : ℚ :=
  if i = 0 then (if j = 0 then -a else if j = 1 then a else 0)
  else if i = 1 then (if j = 0 then b else if j = 1 then -(b + v) else v)
  else 0

def augmentedKillingRowSum (a b v : ℚ) (i : Fin 3) : ℚ :=
  augmentedKillingGenerator a b v i 0 +
    augmentedKillingGenerator a b v i 1 +
    augmentedKillingGenerator a b v i 2

theorem augmented_killing_generator_row_sums (a b v : ℚ) (i : Fin 3) :
    augmentedKillingRowSum a b v i = 0 := by
  fin_cases i
  · simp [augmentedKillingRowSum, augmentedKillingGenerator]
  · simp [augmentedKillingRowSum, augmentedKillingGenerator]
  · simp [augmentedKillingRowSum, augmentedKillingGenerator]

theorem augmented_killing_live_block (a b v : ℚ) :
    augmentedKillingGenerator a b v 0 0 = -a ∧
      augmentedKillingGenerator a b v 0 1 = a ∧
      augmentedKillingGenerator a b v 1 0 = b ∧
      augmentedKillingGenerator a b v 1 1 = -(b + v) := by
  norm_num [augmentedKillingGenerator]

theorem augmented_killing_rate_to_cemetery (a b v : ℚ) :
    augmentedKillingGenerator a b v 1 2 = v := by
  norm_num [augmentedKillingGenerator]

end Book.Chapters.Chapter59
