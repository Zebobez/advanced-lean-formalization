module

public import Book.Models.FiniteTwoState
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib

public section

/-!
# Chapter 45 — Invariant and Reversible Markov Kernels

Extracted from manuscript/chapters/part-07/chapter-45-invariant-and-reversible-markov-kernels.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter45

-- Source Lean fence 2

open Book.Models.FiniteTwoState

theorem uniformLawIsInvariantAtZero : invariantAt uniformWeight flipKernel zero :=
  uniform_flip_invariant_zero

theorem uniformLawSatisfiesDetailedBalance :
    detailedBalanceAt uniformWeight flipKernel zero one :=
  uniform_flip_detailed_balance

-- Source Lean fence 3

theorem exercise_45_3_stationary_mass_zero :
    (2 / 3 : ℚ) * (3 / 4) + (1 / 3) * (1 / 2) = 2 / 3 := by
  norm_num

theorem exercise_45_3_stationary_mass_one :
    (2 / 3 : ℚ) * (1 / 4) + (1 / 3) * (1 / 2) = 1 / 3 := by
  norm_num

theorem exercise_45_3_off_diagonal_balance :
    (2 / 3 : ℚ) * (1 / 4) = (1 / 3) * (1 / 2) := by
  norm_num

-- Source Lean fence 4

open MeasureTheory ProbabilityTheory

theorem exercise_45_5_reversible_markov_kernel_is_invariant
    {α : Type*} [MeasurableSpace α] {κ : Kernel α α} [IsMarkovKernel κ]
    {π : Measure α} (hrev : Kernel.IsReversible κ π) :
    Kernel.Invariant κ π :=
  hrev.invariant

theorem exercise_45_6_composition_preserves_invariance
    {α : Type*} [MeasurableSpace α] {κ η : Kernel α α} {μ : Measure α}
    (hκ : Kernel.Invariant κ μ) (hη : Kernel.Invariant η μ) :
    Kernel.Invariant (κ ∘ₖ η) μ :=
  Kernel.Invariant.comp hκ hη

end Book.Chapters.Chapter45
