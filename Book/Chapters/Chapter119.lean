module

public import Mathlib

public section

/-!
# Chapter 119 — Local Superlinear Convergence and Forcing Terms

Extracted from manuscript/chapters/part-23/chapter-119-local-superlinear-proximal-newton.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter119

-- Source Lean fence 1

theorem local_rate_step
    {e eNext C eta q : ℝ}
    (he : 0 ≤ e)
    (hbound : eNext ≤ C * e ^ 2 + eta * e)
    (hfactor : C * e + eta ≤ q) :
    eNext ≤ q * e := by
  have hmul := mul_le_mul_of_nonneg_right hfactor he
  nlinarith [hbound, hmul]

end Book.Chapters.Chapter119
