module

public import Mathlib

public section

/-!
# Chapter 112 — Douglas–Rachford Splitting and Monotone Inclusions

Extracted from manuscript/chapters/part-23/chapter-112-douglas-rachford-splitting.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter112

-- Source Lean fence 1
def resolventA112 (v : ℚ) : ℚ := max v 0
def reflectedA112 (v : ℚ) : ℚ := 2 * resolventA112 v - v
def resolventB112 (v : ℚ) : ℚ := (v + 2) / 2

def douglasRachford112 (z : ℚ) : ℚ :=
  z - resolventA112 z + resolventB112 (reflectedA112 z)

def shadow112 (z : ℚ) : ℚ := resolventA112 z

theorem dr_step_on_nonnegative_state (z : ℚ) (hz : 0 ≤ z) :
    douglasRachford112 z = (z + 2) / 2 := by
  simp [douglasRachford112, resolventA112, reflectedA112,
    resolventB112, max_eq_left hz]
  ring

theorem first_state_is_zero : douglasRachford112 (-(2 : ℚ)) = 0 := by
  norm_num [douglasRachford112, resolventA112, reflectedA112,
    resolventB112]

theorem second_state_is_one : douglasRachford112 0 = 1 := by
  norm_num [douglasRachford112, resolventA112, reflectedA112,
    resolventB112]

theorem third_state_is_three_halves : douglasRachford112 1 = (3 : ℚ) / 2 := by
  norm_num [douglasRachford112, resolventA112, reflectedA112,
    resolventB112]

theorem fourth_state_is_seven_fourths :
    douglasRachford112 (3 / 2) = (7 : ℚ) / 4 := by
  norm_num [douglasRachford112, resolventA112, reflectedA112,
    resolventB112]

theorem initial_shadow_is_zero : shadow112 (-(2 : ℚ)) = 0 := by
  norm_num [shadow112, resolventA112]

theorem shadow_at_second_state_is_zero : shadow112 0 = 0 := by
  norm_num [shadow112, resolventA112]

theorem shadow_at_third_state_is_one : shadow112 1 = 1 := by
  norm_num [shadow112, resolventA112]

theorem dr_state_two_is_fixed : douglasRachford112 2 = 2 := by
  norm_num [douglasRachford112, resolventA112, reflectedA112,
    resolventB112]

theorem state_error_halves_toward_solution (z : ℚ) (hz : 0 ≤ z) :
    2 - douglasRachford112 z = (2 - z) / 2 := by
  rw [dr_step_on_nonnegative_state z hz]
  ring

end Book.Chapters.Chapter112
