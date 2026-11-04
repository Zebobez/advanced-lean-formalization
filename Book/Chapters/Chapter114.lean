module

public import Mathlib

public section

/-!
# Chapter 114 — Backtracking Proximal Gradient and Local Curvature Certificates

Extracted from manuscript/chapters/part-23/chapter-114-backtracking-proximal-gradient.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter114

-- Source Lean fence 1
def softThreshold114 (z threshold : ℚ) : ℚ :=
  if z < 0 then -max (-z - threshold) 0 else max (z - threshold) 0

def backtrackingCandidate114 (ell : ℚ) : ℚ :=
  softThreshold114 (1 - 4 / ell) (1 / ell)

def smoothObjective114 (x : ℚ) : ℚ := 2 * x ^ 2

def quadraticModel114 (ell candidate : ℚ) : ℚ :=
  smoothObjective114 1 + 4 * (candidate - 1) +
    ell / 2 * (candidate - 1) ^ 2

def compositeObjective114 (x : ℚ) : ℚ := smoothObjective114 x + |x|

theorem first_trial_candidate_is_negative_two :
    backtrackingCandidate114 1 = -2 := by
  norm_num [backtrackingCandidate114, softThreshold114]

theorem first_trial_fails_majorization :
    quadraticModel114 1 (backtrackingCandidate114 1) <
      smoothObjective114 (backtrackingCandidate114 1) := by
  norm_num [quadraticModel114, smoothObjective114,
    backtrackingCandidate114, softThreshold114]

theorem second_trial_candidate_is_negative_half :
    backtrackingCandidate114 2 = -(1 : ℚ) / 2 := by
  norm_num [backtrackingCandidate114, softThreshold114]

theorem second_trial_fails_majorization :
    quadraticModel114 2 (backtrackingCandidate114 2) <
      smoothObjective114 (backtrackingCandidate114 2) := by
  norm_num [quadraticModel114, smoothObjective114,
    backtrackingCandidate114, softThreshold114]

theorem fourth_trial_candidate_is_zero : backtrackingCandidate114 4 = 0 := by
  norm_num [backtrackingCandidate114, softThreshold114]

theorem fourth_trial_is_accepted :
    smoothObjective114 (backtrackingCandidate114 4) ≤
      quadraticModel114 4 (backtrackingCandidate114 4) := by
  norm_num [quadraticModel114, smoothObjective114,
    backtrackingCandidate114, softThreshold114]

theorem zero_is_global_minimizer_of_composite_example (x : ℚ) :
    compositeObjective114 0 ≤ compositeObjective114 x := by
  unfold compositeObjective114 smoothObjective114
  norm_num
  nlinarith [sq_nonneg x, abs_nonneg x]

end Book.Chapters.Chapter114
