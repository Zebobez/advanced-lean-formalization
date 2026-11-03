module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 50 — Gibbs Sampling and Conditional Kernels

Extracted from manuscript/chapters/part-09/chapter-50-gibbs-sampling-and-conditional-kernels.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter50

-- Source Lean fence 1

open Book.Models.FiniteTwoState

theorem gibbsUpdateHasUniformRowAtZero : rowMass resetKernel zero = 2 :=
  reset_zero_row

theorem gibbsUpdateHasUniformRowAtOne : rowMass resetKernel one = 2 :=
  reset_one_row

-- Source Lean fence 2
theorem exercise_50_4_x_given_y_zero :
    (2 : ℚ) / (1 + 2) = 2 / 3 := by norm_num

theorem exercise_50_4_x_given_y_one :
    (4 : ℚ) / (3 + 4) = 4 / 7 := by norm_num

theorem exercise_50_4_y_given_x_zero :
    (3 : ℚ) / (1 + 3) = 3 / 4 := by norm_num

theorem exercise_50_4_y_given_x_one :
    (4 : ℚ) / (2 + 4) = 2 / 3 := by norm_num

theorem exercise_50_3_first_pair_detailed_balance :
    (1 : ℚ) / 10 * (2 / 3) = (2 : ℚ) / 10 * (1 / 3) := by
  norm_num

theorem exercise_50_7_systematic_sweep_forward_flow :
    (1 : ℚ) / 10 * ((2 : ℚ) / 3 * (1 / 3)) = 1 / 45 := by
  norm_num

theorem exercise_50_7_systematic_sweep_reverse_flow :
    (2 : ℚ) / 10 * ((1 : ℚ) / 3 * (1 / 4)) = 1 / 60 := by
  norm_num

theorem exercise_50_7_systematic_sweep_is_not_reversible_at_pair :
    (1 : ℚ) / 45 ≠ 1 / 60 := by
  norm_num

-- Source Lean fence 3
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

theorem exercise_50_6_invariant_updates_compose
    {α : Type*} [MeasurableSpace α] {κ η : Kernel α α} {μ : Measure α}
    (hκ : Kernel.Invariant κ μ) (hη : Kernel.Invariant η μ) :
    Kernel.Invariant (κ ∘ₖ η) μ :=
  Kernel.Invariant.comp hκ hη

theorem exercise_50_8_measure_conditional_kernel_is_markov
    {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (ρ : Measure (Y × X)) [IsFiniteMeasure ρ] :
    IsMarkovKernel (ρ.condKernel : Kernel Y X) := by
  infer_instance

theorem exercise_50_8_conditional_kernel_reconstructs_joint
    {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (ρ : Measure (Y × X)) [IsFiniteMeasure ρ] :
    ρ.fst ⊗ₘ ρ.condKernel = ρ :=
  ρ.disintegrate ρ.condKernel

end Book.Chapters.Chapter50
