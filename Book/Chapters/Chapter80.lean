module

public import Mathlib

public section

/-!
# Chapter 80 — Certified Computation for Matrix-Geometric Tails

Extracted from manuscript/chapters/part-22/chapter-80-certified-computation-qbd.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter80

-- Source Lean fence 1
def certifiedScalarMap (x : ℚ) : ℚ := (2 + 3 * x ^ 2) / 5

theorem certifiedScalarMap_preserves_interval (x : ℚ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 4) :
    0 ≤ certifiedScalarMap x ∧ certifiedScalarMap x ≤ 3 / 4 := by
  have hleft : 0 ≤ 3 / 4 - x := by linarith
  have hright : 0 ≤ 3 / 4 + x := by positivity
  have hx2 : x ^ 2 ≤ (3 / 4 : ℚ) ^ 2 := by
    nlinarith [mul_nonneg hleft hright]
  constructor
  · unfold certifiedScalarMap
    positivity
  · have hupper : certifiedScalarMap x ≤ 59 / 80 := by
      unfold certifiedScalarMap
      nlinarith [hx2]
    exact le_trans hupper (by norm_num)

theorem certifiedScalarMap_difference (x y : ℚ) :
    certifiedScalarMap x - certifiedScalarMap y =
      (3 / 5 : ℚ) * (x - y) * (x + y) := by
  unfold certifiedScalarMap
  ring

theorem certifiedScalarMap_contraction (x y : ℚ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 4)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 3 / 4) :
    |certifiedScalarMap x - certifiedScalarMap y| ≤
      (9 / 10 : ℚ) * |x - y| := by
  by_cases hxy : x ≤ y
  · have hmono : certifiedScalarMap x ≤ certifiedScalarMap y := by
      have hdiff : 0 ≤ certifiedScalarMap y - certifiedScalarMap x := by
        rw [certifiedScalarMap_difference]
        positivity
      exact sub_nonneg.mp hdiff
    have hcontract : certifiedScalarMap y - certifiedScalarMap x ≤
        (9 / 10 : ℚ) * (y - x) := by
      rw [certifiedScalarMap_difference]
      have hbound : 0 ≤ (3 / 2 - (y + x)) * (y - x) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    rw [abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    nlinarith [hcontract]
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hmono : certifiedScalarMap y ≤ certifiedScalarMap x := by
      have hdiff : 0 ≤ certifiedScalarMap x - certifiedScalarMap y := by
        rw [certifiedScalarMap_difference]
        positivity
      exact sub_nonneg.mp hdiff
    have hcontract : certifiedScalarMap x - certifiedScalarMap y ≤
        (9 / 10 : ℚ) * (x - y) := by
      rw [certifiedScalarMap_difference]
      have hbound : 0 ≤ (3 / 2 - (x + y)) * (x - y) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    rw [abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    nlinarith [hcontract]

theorem certifiedScalarMap_fixed : certifiedScalarMap (2 / 3 : ℚ) = 2 / 3 := by
  norm_num [certifiedScalarMap]

theorem certifiedScalarMap_fixed_unique (x : ℚ)
    (hx1 : x ≤ 3 / 4) (hfix : certifiedScalarMap x = x) : x = 2 / 3 := by
  have hpoly : 3 * x ^ 2 - 5 * x + 2 = 0 := by
    unfold certifiedScalarMap at hfix
    nlinarith [hfix]
  have hfactor : (3 * x - 2) * (x - 1) = 0 := by nlinarith [hpoly]
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith

def certifiedScalarIterate : Nat → ℚ
  | 0 => 0
  | n + 1 => certifiedScalarMap (certifiedScalarIterate n)

theorem certifiedScalarIterate_in_interval (n : Nat) :
    0 ≤ certifiedScalarIterate n ∧ certifiedScalarIterate n ≤ 3 / 4 := by
  induction n with
  | zero => norm_num [certifiedScalarIterate]
  | succ n ih =>
      simpa [certifiedScalarIterate] using
        certifiedScalarMap_preserves_interval (certifiedScalarIterate n) ih.1 ih.2

theorem certifiedScalarIterate_error (n : Nat) :
    |certifiedScalarIterate n - 2 / 3| ≤ 4 * (9 / 10 : ℚ) ^ n := by
  induction n with
  | zero => norm_num [certifiedScalarIterate]
  | succ n ih =>
      have hI := certifiedScalarIterate_in_interval n
      calc
        |certifiedScalarIterate (n + 1) - 2 / 3| =
            |certifiedScalarMap (certifiedScalarIterate n) -
              certifiedScalarMap (2 / 3)| := by
                rw [certifiedScalarIterate, certifiedScalarMap_fixed]
        _ ≤ (9 / 10 : ℚ) *
            |certifiedScalarIterate n - 2 / 3| :=
              certifiedScalarMap_contraction (certifiedScalarIterate n) (2 / 3)
                hI.1 hI.2 (by norm_num) (by norm_num)
        _ ≤ (9 / 10 : ℚ) * (4 * (9 / 10 : ℚ) ^ n) :=
              mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 4 * (9 / 10 : ℚ) ^ (n + 1) := by rw [pow_succ]; ring

theorem certifiedFirstIterate : certifiedScalarIterate 1 = 2 / 5 := by
  norm_num [certifiedScalarIterate, certifiedScalarMap]

theorem certifiedTailBoundAtTwenty :
    (1 / 5 : ℚ) * (7 / 10 : ℚ) ^ 20 / (1 - 7 / 10) < 532 / 1000000 := by
  norm_num

end Book.Chapters.Chapter80
