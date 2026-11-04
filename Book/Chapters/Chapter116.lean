module

public import Mathlib

public section

/-!
# Chapter 116 — Proximal Quasi-Newton Methods and Structured Metrics

Extracted from manuscript/chapters/part-23/chapter-116-proximal-quasi-newton.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter116

-- Source Lean fence 1
def softThreshold116 (z threshold : ℚ) : ℚ :=
  if z < 0 then -max (-z - threshold) 0 else max (z - threshold) 0

def lowRankPrimal116 (q : ℚ) : ℚ × ℚ :=
  (softThreshold116 (2 - q) (1 / 2), softThreshold116 (-q) (1 / 2))

def lowRankDualMap116 (q : ℚ) : ℚ :=
  (lowRankPrimal116 q).1 + (lowRankPrimal116 q).2 - 2

def lowRankCandidate116 : ℚ × ℚ := ((7 : ℚ) / 4, 0)

theorem dual_variable_solves_low_rank_equation :
    lowRankDualMap116 (-(1 : ℚ) / 4) = -(1 : ℚ) / 4 := by
  norm_num [lowRankDualMap116, lowRankPrimal116, softThreshold116]

theorem low_rank_primal_point :
    lowRankPrimal116 (-(1 : ℚ) / 4) = lowRankCandidate116 := by
  norm_num [lowRankPrimal116, lowRankCandidate116, softThreshold116]

theorem euclidean_proximal_point_is_different :
    (softThreshold116 2 (1 / 2), softThreshold116 0 (1 / 2)) =
      ((3 : ℚ) / 2, 0) := by
  norm_num [softThreshold116]

def lowRankMetricObjective116 (x : ℚ × ℚ) : ℚ :=
  ((x.1 - 2) ^ 2 + x.2 ^ 2 + (x.1 + x.2 - 2) ^ 2) / 2 +
    (|x.1| + |x.2|) / 2

theorem low_rank_point_is_global_metric_proximum (x : ℚ × ℚ) :
    lowRankMetricObjective116 lowRankCandidate116 ≤
      lowRankMetricObjective116 x := by
  have hFirst : 0 ≤ |x.1| - (7 : ℚ) / 4 - (x.1 - 7 / 4) := by
    have h := le_abs_self x.1
    linarith
  have hSecond : 0 ≤ |x.2| - x.2 / 2 := by
    by_cases hx : 0 ≤ x.2
    · rw [abs_of_nonneg hx]
      nlinarith
    · have hx' : x.2 ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx']
      nlinarith
  norm_num [lowRankMetricObjective116, lowRankCandidate116]
  nlinarith [hFirst, hSecond, sq_nonneg (x.1 - 7 / 4),
    sq_nonneg x.2, sq_nonneg (x.1 + x.2 - 7 / 4)]

end Book.Chapters.Chapter116
