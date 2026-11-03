module

public import Mathlib

public section

/-!
# Chapter 84 — GI/M/1-Type Chains and Geometric Stationary Tails

Extracted from manuscript/chapters/part-22/chapter-84-gi-m1-type-chains-and-geometric-tails.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter84

-- Source Lean fence 1
def giRateMap (r : ℚ) : ℚ := 1 / 10 + (1 / 5) * r + (7 / 10) * r ^ 2

def giGeometricWeight (n : Nat) : ℚ := (6 / 7) * (1 / 7 : ℚ) ^ n

theorem giRateMap_factorization (r : ℚ) :
    giRateMap r - r = ((7 * r - 1) * (r - 1)) / 10 := by
  unfold giRateMap
  ring

theorem giRate_is_fixed_point : giRateMap (1 / 7) = 1 / 7 := by
  norm_num [giRateMap]

theorem giRate_one_is_fixed_point : giRateMap 1 = 1 := by
  norm_num [giRateMap]

theorem giBoundary_row_sum : 9 / 10 + 1 / 10 = (1 : ℚ) := by norm_num

theorem giPositive_row_sum : 7 / 10 + 1 / 5 + 1 / 10 = (1 : ℚ) := by norm_num

theorem giBoundary_local_balance :
    (9 / 10 : ℚ) * giGeometricWeight 0 +
      (7 / 10 : ℚ) * giGeometricWeight 1 = giGeometricWeight 0 := by
  norm_num [giGeometricWeight]

theorem giLevelOne_local_balance :
    (1 / 10 : ℚ) * giGeometricWeight 0 +
      (1 / 5 : ℚ) * giGeometricWeight 1 +
      (7 / 10 : ℚ) * giGeometricWeight 2 = giGeometricWeight 1 := by
  norm_num [giGeometricWeight]

theorem giGeometricWeight_succ (n : Nat) :
    giGeometricWeight (n + 1) = giGeometricWeight n / 7 := by
  unfold giGeometricWeight
  rw [pow_succ]
  ring

theorem giInterior_local_balance (n : Nat) (hn : 2 ≤ n) :
    (1 / 10 : ℚ) * giGeometricWeight (n - 1) +
      (1 / 5 : ℚ) * giGeometricWeight n +
      (7 / 10 : ℚ) * giGeometricWeight (n + 1) = giGeometricWeight n := by
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hprev := giGeometricWeight_succ (n - 1)
  rw [hsub] at hprev
  have hnext := giGeometricWeight_succ n
  have hfactor : giGeometricWeight (n - 1) = 7 * giGeometricWeight n := by
    nlinarith [hprev]
  rw [hfactor, hnext]
  norm_num
  ring

theorem giGeometricWeight_nonnegative (n : Nat) : 0 ≤ giGeometricWeight n := by
  unfold giGeometricWeight
  exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) n)

end Book.Chapters.Chapter84
