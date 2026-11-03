module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 73 — Regeneration and Renewal Rewards

Extracted from manuscript/chapters/part-18/chapter-73-regeneration-and-renewal-rewards.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter73

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def cycleReward : Weight := fun s => if s = zero then 2 else 1
def cycleLength : Nat := totalWeight uniformWeight

theorem oneCycleReward : totalWeight cycleReward = 3 := by decide
theorem oneCycleLength : cycleLength = 2 := by decide

-- Source Lean fence 3
def cycleOccupationZero (a : ℚ) : ℚ := 1 / a
def cycleOccupationOne (b : ℚ) : ℚ := 1 / b

def twoStateCycleLength (a b : ℚ) : ℚ :=
  cycleOccupationZero a + cycleOccupationOne b

def cycleStationaryZero (a b : ℚ) : ℚ :=
  cycleOccupationZero a / twoStateCycleLength a b

def cycleStationaryOne (a b : ℚ) : ℚ :=
  cycleOccupationOne b / twoStateCycleLength a b

theorem cycleStationaryZero_eq (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    cycleStationaryZero a b = b / (a + b) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  unfold cycleStationaryZero twoStateCycleLength cycleOccupationZero cycleOccupationOne
  field_simp [ha', hb']
  ring

theorem cycleStationaryOne_eq (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    cycleStationaryOne a b = a / (a + b) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  unfold cycleStationaryOne twoStateCycleLength cycleOccupationZero cycleOccupationOne
  field_simp [ha', hb']
  ring

theorem cycleStationary_normalized (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    cycleStationaryZero a b + cycleStationaryOne a b = 1 := by
  rw [cycleStationaryZero_eq a b ha hb, cycleStationaryOne_eq a b ha hb]
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  field_simp [hab]
  ring

theorem cycleStationary_balanced_flow (a b : ℚ)
    (ha : 0 < a) (hb : 0 < b) :
    cycleStationaryZero a b * a = cycleStationaryOne a b * b := by
  rw [cycleStationaryZero_eq a b ha hb, cycleStationaryOne_eq a b ha hb]
  ring

end Book.Chapters.Chapter73
