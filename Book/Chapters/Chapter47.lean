module

public import Book.Models.FiniteTwoState
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.Ergodic.EmpiricalMeasure
public import Mathlib

public section

/-!
# Chapter 47 — Ergodic Averages and Empirical Measures

Extracted from manuscript/chapters/part-07/chapter-47-ergodic-averages-and-empirical-measures.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter47

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def orbitObservable : State → Int := fun s => if s = zero then 0 else 2

theorem twoPointOrbitAverageNumerator :
    expectationNumerator uniformWeight orbitObservable = 2 := by decide

-- Source Lean fence 3

theorem exercise_47_2_average_at_zero_is_zero
    {R α M : Type*} [DivisionSemiring R] [AddCommMonoid M] [Module R M]
    (f : α → α) (g : α → M) : birkhoffAverage R f g 0 = 0 := by
  exact birkhoffAverage_zero R f g

theorem exercise_47_3_fixed_point_average
    {R α M : Type*} [DivisionSemiring R] [AddCommMonoid M] [Module R M]
    {f : α → α} {x : α} (hx : Function.IsFixedPt f x)
    (g : α → M) {n : ℕ} (hn : (n : R) ≠ 0) :
    birkhoffAverage R f g n x = g x :=
  hx.birkhoffAverage_eq R g hn

-- Source Lean fence 4

open MeasureTheory

theorem exercise_47_6_empirical_integral_is_orbit_average
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (f : X → X) (x : X) (n : ℕ) (g : X → ℝ) :
    ∫ y, g y ∂MeasureTheory.empiricalMeasure f x n =
      birkhoffAverage NNReal f g (n + 1) x :=
  MeasureTheory.integral_empiricalMeasure_eq_birkhoffaverage
    (f := f) (x := x) (g := g) n

theorem exercise_47_9_krylov_bogolyubov
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [CompactSpace X] [Nonempty X] {f : X → X}
    (hf : Continuous f) :
    ∃ μ : Measure X, MeasurePreserving f μ μ ∧
      Measure.Regular μ ∧ IsProbabilityMeasure μ :=
  MeasureTheory.exists_measurePreserving_probabilityMeasure hf

end Book.Chapters.Chapter47
