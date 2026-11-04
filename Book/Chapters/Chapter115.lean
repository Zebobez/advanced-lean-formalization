module

public import Mathlib

public section

/-!
# Chapter 115 — Variable-Metric Forward–Backward Splitting

Extracted from manuscript/chapters/part-23/chapter-115-variable-metric-forward-backward.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter115

-- Source Lean fence 1
def softThreshold115 (z threshold : ℚ) : ℚ :=
  if z < 0 then -max (-z - threshold) 0 else max (z - threshold) 0

def diagonalForward115 (x1 x2 : ℚ) : ℚ × ℚ :=
  (x1 - 1 * (x1 - 2), x2 - (1 / 4) * (4 * (x2 + 1)))

def diagonalMetricProx115 (v : ℚ × ℚ) : ℚ × ℚ :=
  (softThreshold115 v.1 (1 / 2), softThreshold115 v.2 (1 / 8))

def variableMetricStep115 (x1 x2 : ℚ) : ℚ × ℚ :=
  diagonalMetricProx115 (diagonalForward115 x1 x2)

theorem diagonal_forward_point_is_data (x1 x2 : ℚ) :
    diagonalForward115 x1 x2 = (2, -1) := by
  ext <;> simp [diagonalForward115]

theorem diagonal_metric_prox_at_data :
    diagonalMetricProx115 (2, -1) = ((3 : ℚ) / 2, -(7 : ℚ) / 8) := by
  norm_num [diagonalMetricProx115, softThreshold115]

theorem one_variable_metric_step_solves_example (x1 x2 : ℚ) :
    variableMetricStep115 x1 x2 = ((3 : ℚ) / 2, -(7 : ℚ) / 8) := by
  unfold variableMetricStep115
  rw [diagonal_forward_point_is_data]
  exact diagonal_metric_prox_at_data

end Book.Chapters.Chapter115
