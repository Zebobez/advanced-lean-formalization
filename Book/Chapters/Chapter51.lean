module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 51 — Importance Sampling and Change of Measure

Extracted from manuscript/chapters/part-10/chapter-51-importance-sampling-and-change-of-measure.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter51

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def proposal : Weight := uniformWeight
def importanceLikelihood : Weight := fun s => if s = zero then 2 else 1
def weightedSample : Weight := fun s => proposal s * importanceLikelihood s

theorem importanceWeightNormalizer : totalWeight weightedSample = 3 := by decide
theorem weightedMassAtZero : weightedSample zero = 2 := by decide

-- Source Lean fence 2
open MeasureTheory
open scoped ENNReal

theorem exercise_51_1_lintegral_change_of_measure
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) {f : X → ℝ≥0∞} (hf : AEMeasurable f ν) :
    ∫⁻ x, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x, f x ∂μ :=
  MeasureTheory.lintegral_rnDeriv_mul hμν hf

theorem exercise_51_8_real_change_of_measure
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [Measure.HaveLebesgueDecomposition μ ν] [SigmaFinite μ]
    (hμν : μ ≪ ν) {f : X → ℝ} :
    ∫ x, (μ.rnDeriv ν x).toReal * f x ∂ν = ∫ x, f x ∂μ :=
  MeasureTheory.integral_toReal_rnDeriv_mul hμν

theorem exercise_51_10_pmf_expectation_finite_sum
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype X] (p : PMF X) (f : X → ℝ) :
    ∫ x, f x ∂p.toMeasure = ∑ x, (p x).toReal * f x := by
  simpa [smul_eq_mul] using PMF.integral_eq_sum p f

theorem exercise_51_4_three_state_target_normalizes :
    (1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1 := by
  norm_num

theorem exercise_51_4_weighted_indicator_is_unbiased :
    (1 : ℚ) / 3 * ((1 / 2 : ℚ) / (1 / 3)) = 1 / 2 := by
  norm_num

theorem exercise_51_6_one_sample_self_normalized_estimator_is_biased :
    (1 : ℚ) / 2 ≠ 9 / 10 := by
  norm_num

end Book.Chapters.Chapter51
