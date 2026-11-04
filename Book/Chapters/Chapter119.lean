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

theorem geometric_error_bound
    {e : ℕ → ℝ} {q : ℝ}
    (hq : 0 ≤ q)
    (hstep : ∀ k, e (k + 1) ≤ q * e k)
    (n : ℕ) :
    e n ≤ q ^ n * e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        e (n + 1) ≤ q * e n := hstep n
        _ ≤ q * (q ^ n * e 0) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * e 0 := by rw [pow_succ]; ring

end Book.Chapters.Chapter119
