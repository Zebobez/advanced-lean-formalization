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

theorem kl_recurrence_of_certificates
    {a b sPrev sCurr slope grad gap drop : ℝ}
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (hPrev : 0 ≤ sPrev)
    (hSlope : 0 ≤ slope)
    (hGap : 0 ≤ gap)
    (hKL : 1 ≤ slope * grad)
    (hRelative : grad ≤ b * sPrev)
    (hDecrease : a * sCurr ^ 2 ≤ gap)
    (hConcavity : slope * gap ≤ drop) :
    2 * sCurr ≤ sPrev + (b / a) * drop := by
  have hproduct := kl_product_bound_of_certificates ha.le hb hPrev hSlope hKL
    hRelative hDecrease hConcavity
  have hdrop : 0 ≤ drop := le_trans (mul_nonneg hSlope hGap) hConcavity
  have hscaled : 0 ≤ (b / a) * drop :=
    mul_nonneg (div_nonneg hb (le_of_lt ha)) hdrop
  have hscale : a * (sPrev * ((b / a) * drop)) = b * sPrev * drop := by
    field_simp [ne_of_gt ha]
  have hcross : a * sCurr ^ 2 ≤ a * (sPrev * ((b / a) * drop)) := by
    rw [hscale]
    exact hproduct
  have hbound : sCurr ^ 2 ≤ sPrev * ((b / a) * drop) :=
    (mul_le_mul_iff_of_pos_left ha).mp hcross
  exact kl_length_recurrence hPrev hscaled hbound

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

theorem summable_real_tendsto_zero {f : ℕ → ℝ} (hf : Summable f) :
    Tendsto f atTop (𝓝 0) := by
  have hsum := hf.hasSum.tendsto_sum_nat
  have hsumSucc := hsum.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto
      (fun n => (∑ i ∈ Finset.range (n + 1), f i) - ∑ i ∈ Finset.range n, f i)
      atTop (𝓝 0) := by
    simpa using hsumSucc.sub hsum
  simpa only [Finset.sum_range_succ, add_sub_cancel_left] using hdiff

theorem relative_error_witness_tendsto_zero
    {E : Type*} [NormedAddCommGroup E]
    (s : ℕ → ℝ) (w : ℕ → E) (b : ℝ)
    (hs : Summable s)
    (hrelative : ∀ n, ‖w n‖ ≤ b * s n) :
    Tendsto w atTop (𝓝 0) := by
  have hs0 := summable_real_tendsto_zero hs
  have hbound : Tendsto (fun n => b * s n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hs0)
  have hwnorm := squeeze_zero (fun n => norm_nonneg (w n)) hrelative hbound
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa [dist_eq_norm] using hwnorm

theorem closed_relation_limit
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (R : X → Y → Prop)
    (hclosed : IsClosed {p : X × Y | R p.1 p.2})
    (x : ℕ → X) (w : ℕ → Y) (xLimit : X) (yLimit : Y)
    (hx : Tendsto x atTop (𝓝 xLimit))
    (hw : Tendsto w atTop (𝓝 yLimit))
    (hR : ∀ n, R (x n) (w n)) :
    R xLimit yLimit := by
  have hpair : Tendsto (fun n => (x n, w n)) atTop (𝓝 (xLimit, yLimit)) :=
    hx.prodMk_nhds hw
  exact hclosed.mem_of_tendsto hpair (Filter.Eventually.of_forall hR)

theorem closed_relation_limit_of_relative_error
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (R : X → E → Prop)
    (hclosed : IsClosed {p : X × E | R p.1 p.2})
    (x : ℕ → X) (w : ℕ → E) (s : ℕ → ℝ) (b : ℝ) (xLimit : X)
    (hx : Tendsto x atTop (𝓝 xLimit))
    (hs : Summable s)
    (hrelative : ∀ n, ‖w n‖ ≤ b * s n)
    (hR : ∀ n, R (x n) (w n)) :
    R xLimit 0 := by
  exact closed_relation_limit R hclosed x w xLimit 0 hx
    (relative_error_witness_tendsto_zero s w b hs hrelative) hR

theorem kl_certificates_imply_convergence
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    (x : ℕ → X) (s phi slope grad gap : ℕ → ℝ)
    (a b lower : ℝ)
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (hphi : ∀ n, lower ≤ phi n)
    (hs : ∀ n, 0 ≤ s n)
    (hstepDistance : ∀ n, dist (x n) (x n.succ) ≤ s n)
    (hSlope : ∀ n, 0 ≤ slope n)
    (hGap : ∀ n, 0 ≤ gap n)
    (hKL : ∀ n, 1 ≤ slope n * grad n)
    (hRelative : ∀ n, grad n ≤ b * s n)
    (hDecrease : ∀ n, a * s (n + 1) ^ 2 ≤ gap n)
    (hConcavity : ∀ n, slope n * gap n ≤ phi n - phi (n + 1)) :
    ∃ xLimit, Tendsto x atTop (𝓝 xLimit) := by
  have hrecurrence : ∀ n, 2 * s (n + 1) ≤ s n + (b / a) * (phi n - phi (n + 1)) := by
    intro n
    exact kl_recurrence_of_certificates ha hb (hs n) (hSlope n) (hGap n)
      (hKL n) (hRelative n) (hDecrease n) (hConcavity n)
  have hlength : Summable s :=
    kl_recurrence_summable s phi (b / a) lower (div_nonneg hb ha.le)
      hphi hs hrecurrence
  have hcauchy : CauchySeq x :=
    cauchySeq_of_dist_le_of_summable s hstepDistance hlength
  exact cauchySeq_tendsto_of_complete hcauchy

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
