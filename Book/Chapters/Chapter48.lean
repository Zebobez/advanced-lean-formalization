module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 48 — Total Variation and Markov Chain Convergence

Extracted from manuscript/chapters/part-08/chapter-48-total-variation-and-markov-chain-convergence.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter48

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def pointMassZero : Weight := fun s => if s = zero then 1 else 0
def pointMassOne : Weight := fun s => if s = one then 1 else 0
def absoluteMassDifference (a b : Nat) : Nat := (a - b) + (b - a)
def totalVariationNumerator : Nat :=
  absoluteMassDifference (pointMassZero zero) (pointMassOne zero) +
  absoluteMassDifference (pointMassZero one) (pointMassOne one)

theorem distinctPointMassesHaveDistanceTwo : totalVariationNumerator = 2 := by decide

-- Source Lean fence 2
theorem exercise_48_1_tvDist_triangle
    {X : Type*} [MeasurableSpace X]
    (μ ν ξ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure ν] :
    MeasureTheory.tvDist μ ξ ≤
      MeasureTheory.tvDist μ ν + MeasureTheory.tvDist ν ξ :=
  MeasureTheory.tvDist_triangle μ ν ξ

theorem exercise_48_12_tvDist_zero_characterization
    {X : Type*} [MeasurableSpace X]
    (μ ν : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν] :
    MeasureTheory.tvDist μ ν = 0 ↔ μ = ν :=
  MeasureTheory.tvDist_eq_zero_iff

theorem tvDist_distinct_dirac_eq_two
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {x y : X} (hxy : x ≠ y) :
    MeasureTheory.tvDist (MeasureTheory.Measure.dirac x)
      (MeasureTheory.Measure.dirac y) = 2 := by
  have hsingular :
      MeasureTheory.Measure.MutuallySingular
        (MeasureTheory.Measure.dirac x) (MeasureTheory.Measure.dirac y) := by
    refine ⟨{y}, MeasurableSet.singleton y, ?_, ?_⟩
    · simp [hxy]
    · simp
  rw [MeasureTheory.tvDist_of_mutuallySingular hsingular]
  norm_num

end Book.Chapters.Chapter48
