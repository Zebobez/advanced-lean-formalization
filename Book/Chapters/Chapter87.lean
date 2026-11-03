module

public import Mathlib

public section

/-!
# Chapter 87 — Monotone Construction of the Rate Matrix

Extracted from manuscript/chapters/part-22/chapter-87-monotone-rate-matrix-iteration.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter87

-- Source Lean fence 1
def scalarRateMap (x : ℚ) : ℚ := 1 / 10 + (1 / 5) * x + (7 / 10) * x ^ 2

def scalarRateIterate : Nat → ℚ
  | 0 => 0
  | n + 1 => scalarRateMap (scalarRateIterate n)

theorem scalarRateMap_nonnegative {x : ℚ} (hx : 0 ≤ x) :
    0 ≤ scalarRateMap x := by
  unfold scalarRateMap
  positivity

theorem scalarRateMap_difference (x y : ℚ) :
    scalarRateMap y - scalarRateMap x =
      (y - x) * (1 / 5 + (7 / 10 : ℚ) * (x + y)) := by
  unfold scalarRateMap
  ring

theorem scalarRateMap_monotone {x y : ℚ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    scalarRateMap x ≤ scalarRateMap y := by
  have hdiff : 0 ≤ scalarRateMap y - scalarRateMap x := by
    rw [scalarRateMap_difference]
    have hyx : 0 ≤ y - x := sub_nonneg.mpr hxy
    have hsum : 0 ≤ x + y := by linarith
    positivity
  exact sub_nonneg.mp hdiff

theorem scalarRateIterate_nonnegative (n : Nat) : 0 ≤ scalarRateIterate n := by
  induction n with
  | zero => norm_num [scalarRateIterate]
  | succ n ih =>
      simpa [scalarRateIterate] using scalarRateMap_nonnegative ih

theorem scalarRateIterate_le_succ (n : Nat) :
    scalarRateIterate n ≤ scalarRateIterate (n + 1) := by
  induction n with
  | zero => norm_num [scalarRateIterate, scalarRateMap]
  | succ n ih =>
      simpa [scalarRateIterate] using
        scalarRateMap_monotone (scalarRateIterate_nonnegative n) ih

theorem scalarRateMap_supersolution : scalarRateMap (3 / 20) ≤ 3 / 20 := by
  norm_num [scalarRateMap]

theorem scalarRateIterate_le_supersolution (n : Nat) :
    scalarRateIterate n ≤ 3 / 20 := by
  induction n with
  | zero => norm_num [scalarRateIterate]
  | succ n ih =>
      have hmap := scalarRateMap_monotone (scalarRateIterate_nonnegative n) ih
      have hsup := scalarRateMap_supersolution
      simpa [scalarRateIterate] using le_trans hmap hsup

theorem scalarRateIterate_one : scalarRateIterate 1 = 1 / 10 := by
  norm_num [scalarRateIterate, scalarRateMap]

theorem scalarRateIterate_two : scalarRateIterate 2 = 127 / 1000 := by
  norm_num [scalarRateIterate, scalarRateMap]

theorem scalarRateIterate_three : scalarRateIterate 3 = 1366903 / 10000000 := by
  norm_num [scalarRateIterate, scalarRateMap]

theorem scalarRateRoot_fixed : scalarRateMap (1 / 7) = 1 / 7 := by
  norm_num [scalarRateMap]

theorem scalarRateResidual_factorization (x : ℚ) :
    scalarRateMap x - x = ((7 * x - 1) * (x - 1)) / 10 := by
  unfold scalarRateMap
  ring

theorem scalarRateRoot_bracket :
    scalarRateIterate 3 ≤ 1 / 7 ∧ 1 / 7 ≤ 3 / 20 := by
  norm_num [scalarRateIterate_three]

end Book.Chapters.Chapter87
