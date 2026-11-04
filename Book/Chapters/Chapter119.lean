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

open Filter
open scoped Topology

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

theorem geometric_error_tendsto_zero
    {e : ℕ → ℝ} {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (he : ∀ n, 0 ≤ e n)
    (hstep : ∀ k, e (k + 1) ≤ q * e k) :
    Tendsto e atTop (𝓝 0) := by
  have hbound := geometric_error_bound hq0 hstep
  have hpow : Tendsto (fun n : ℕ => q ^ n * e 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (e 0)
  exact squeeze_zero (fun n => he n) (fun n => hbound n) hpow

theorem superlinear_error_ratio
    {e eta : ℕ → ℝ} {C : ℝ}
    (hepos : ∀ n, 0 < e n)
    (he_tendsto : Tendsto e atTop (𝓝 0))
    (heta_tendsto : Tendsto eta atTop (𝓝 0))
    (hstep : ∀ n, e (n + 1) ≤ C * e n ^ 2 + eta n * e n) :
    Tendsto (fun n => e (n + 1) / e n) atTop (𝓝 0) := by
  have hratio : ∀ n, e (n + 1) / e n ≤ C * e n + eta n := by
    intro n
    apply (div_le_iff₀ (hepos n)).2
    nlinarith [hstep n]
  have hupper : Tendsto (fun n => C * e n + eta n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul he_tendsto).add heta_tendsto
  exact squeeze_zero
    (fun n => div_nonneg (le_of_lt (hepos (n + 1))) (le_of_lt (hepos n)))
    hratio hupper

end Book.Chapters.Chapter119
