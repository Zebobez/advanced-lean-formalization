module

public import Mathlib

public section

/-!
# Chapter 120 — Kurdyka–Łojasiewicz Convergence and Finite Length

Extracted from manuscript/chapters/part-23/chapter-120-kurdyka-lojasiewicz-convergence.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter120

-- Source Lean fence 1

open Filter
open scoped Topology

theorem finite_descent_budget
    (F q : ℕ → ℝ) (a lower : ℝ)
    (h_lower : ∀ n, lower ≤ F n)
    (h_step : ∀ n, F (n + 1) + a * q n ≤ F n)
    (N : ℕ) :
    a * ∑ n ∈ Finset.range N, q n ≤ F 0 - lower := by
  have htel : ∀ N, F N + a * ∑ n ∈ Finset.range N, q n ≤ F 0 := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        nlinarith [h_step N]
  have h := htel N
  have hl := h_lower N
  linarith

theorem kl_length_recurrence
    {sPrev sCurr scaledDrop : ℝ}
    (hPrev : 0 ≤ sPrev)
    (hDrop : 0 ≤ scaledDrop)
    (hProduct : sCurr ^ 2 ≤ sPrev * scaledDrop) :
    2 * sCurr ≤ sPrev + scaledDrop := by
  nlinarith [sq_nonneg (sPrev - scaledDrop)]

theorem kl_product_bound_of_certificates
    {a b sPrev sCurr slope grad gap drop : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hPrev : 0 ≤ sPrev)
    (hSlope : 0 ≤ slope)
    (hKL : 1 ≤ slope * grad)
    (hRelative : grad ≤ b * sPrev)
    (hDecrease : a * sCurr ^ 2 ≤ gap)
    (hConcavity : slope * gap ≤ drop) :
    a * sCurr ^ 2 ≤ b * sPrev * drop := by
  have hgradScaled := mul_le_mul_of_nonneg_left hRelative hSlope
  have hfactor : 1 ≤ slope * (b * sPrev) := by
    nlinarith [hKL, hgradScaled]
  have hdecreaseScaled := mul_le_mul_of_nonneg_left hDecrease hSlope
  have hstepScaled : slope * (a * sCurr ^ 2) ≤ drop := by
    nlinarith [hdecreaseScaled, hConcavity]
  have hfromFactor :=
    mul_le_mul_of_nonneg_right hfactor (mul_nonneg ha (sq_nonneg sCurr))
  have htoDrop := mul_le_mul_of_nonneg_left hstepScaled (mul_nonneg hb hPrev)
  nlinarith [hfromFactor, htoDrop]

theorem kl_partial_sum_bound
    (s phi : ℕ → ℝ) (c : ℝ)
    (hstep : ∀ k, 2 * s (k + 1) ≤ s k + c * (phi k - phi (k + 1)))
    (hs : ∀ k, 0 ≤ s k) (N : ℕ) :
    ∑ k ∈ Finset.range N, s (k + 1) ≤ s 0 + c * (phi 0 - phi N) := by
  have htel : ∀ N, (∑ k ∈ Finset.range N, s (k + 1)) + s N ≤
      s 0 + c * (phi 0 - phi N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        nlinarith [hstep N]
  have h := htel N
  linarith [hs N]

theorem kl_recurrence_summable
    (s phi : ℕ → ℝ) (c lower : ℝ)
    (hc : 0 ≤ c)
    (hphi : ∀ n, lower ≤ phi n)
    (hs : ∀ n, 0 ≤ s n)
    (hstep : ∀ k, 2 * s (k + 1) ≤ s k + c * (phi k - phi (k + 1))) :
    Summable s := by
  have hbound : ∀ N, ∑ k ∈ Finset.range N, s (k + 1) ≤
      s 0 + c * (phi 0 - lower) := by
    intro N
    have htel := kl_partial_sum_bound s phi c hstep hs N
    have hmul := mul_le_mul_of_nonneg_left (hphi N) hc
    nlinarith [htel, hs N]
  have htail : Summable fun n => s (n + 1) :=
    summable_of_sum_range_le (fun n => hs (n + 1)) hbound
  exact (summable_nat_add_iff (f := s) 1).mp htail

theorem finite_length_sequence_is_cauchy {X : Type*} [PseudoMetricSpace X]
    (x : ℕ → X)
    (h_length : Summable fun n => dist (x n) (x n.succ)) :
    CauchySeq x :=
  cauchySeq_of_summable_dist h_length

theorem finite_length_sequence_converges {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] (x : ℕ → X)
    (h_length : Summable fun n => dist (x n) (x n.succ)) :
    ∃ xLimit, Tendsto x atTop (𝓝 xLimit) :=
  cauchySeq_tendsto_of_complete (finite_length_sequence_is_cauchy x h_length)

end Book.Chapters.Chapter120
