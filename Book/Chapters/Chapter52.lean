module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 52 — Variance and Monte Carlo Error Bounds

Extracted from manuscript/chapters/part-10/chapter-52-variance-and-monte-carlo-error.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter52

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def centeredSample : State → Int := fun s => if s = zero then -1 else 1
def squaredSample (s : State) : Int := centeredSample s * centeredSample s

theorem bernoulliSampleHasZeroMean :
    expectationNumerator uniformWeight centeredSample = 0 := by decide

theorem bernoulliSampleHasSecondMomentTwo :
    expectationNumerator uniformWeight squaredSample = 2 := by decide

-- Source Lean fence 2
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

theorem exercise_52_2_independent_sum_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hXY : X ⟂ᵢ[μ] Y) :
    variance (fun ω => X ω + Y ω) μ = variance X μ + variance Y μ :=
  hXY.variance_fun_add hX hY

theorem exercise_52_2_variance_scales_quadratically
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ) :
    variance (fun ω => c * X ω) μ = c ^ 2 * variance X μ :=
  variance_const_mul c X μ

theorem exercise_52_4_chebyshev
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |X ω - μ[X]|} ≤
      ENNReal.ofReal (variance X μ / ε ^ 2) :=
  meas_ge_le_variance_div_sq hX hε

theorem exercise_52_5_bounded_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hRange : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ ((b - a) / 2) ^ 2 :=
  variance_le_sq_of_bounded hRange hX

theorem exercise_52_6_fair_bernoulli_variance :
    (1 : ℚ) / 2 * (1 - 1 / 2) = 1 / 4 := by
  norm_num

theorem exercise_52_6_two_sample_average_variance :
    (1 : ℚ) / 4 / 2 = 1 / 8 := by
  norm_num

end Book.Chapters.Chapter52
