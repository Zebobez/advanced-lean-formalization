module

public import Book.Models.FiniteTwoState
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Function
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib

public section

/-!
# Chapter 46 — Measure-Preserving Dynamics and Ergodicity

Extracted from manuscript/chapters/part-07/chapter-46-measure-preserving-dynamics-and-ergodicity.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter46

-- Source Lean fence 3

open Book.Models.FiniteTwoState

def rotation (s : State) : State := if s = zero then one else zero
def rotatedUniformMass (s : State) : Nat := uniformWeight (rotation s)

theorem rotationPreservesMassAtZero : rotatedUniformMass zero = 1 := by decide
theorem rotationPreservesMassAtOne : rotatedUniformMass one = 1 := by decide

-- Source Lean fence 4

open MeasureTheory

theorem exercise_46_1_measure_preserving_comp
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    {f : α → β} {g : β → γ}
    (hg : MeasurePreserving g ν ξ) (hf : MeasurePreserving f μ ν) :
    MeasurePreserving (g ∘ f) μ ξ :=
  hg.comp hf

theorem exercise_46_1_measure_preserving_iterate
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}
    (hf : MeasurePreserving f μ μ) (n : ℕ) :
    MeasurePreserving f^[n] μ μ :=
  hf.iterate n

-- Source Lean fence 5

open Filter MeasureTheory

theorem exercise_46_2_ergodic_set_is_ae_trivial
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}
    (h : Ergodic f μ) {s : Set α}
    (hs : NullMeasurableSet s μ) (hinv : f ⁻¹' s =ᵐ[μ] s) :
    s =ᵐ[μ] ∅ ∨ s =ᵐ[μ] Set.univ :=
  h.toPreErgodic.ae_empty_or_univ hs hinv

theorem exercise_46_5_invariant_observable_is_ae_constant
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}
    (h : Ergodic f μ) {g : α → ℝ}
    (hgm : AEStronglyMeasurable g μ) (hinv : g ∘ f =ᵐ[μ] g) :
    ∃ c, g =ᵐ[μ] fun _ => c :=
  h.ae_eq_const_of_ae_eq_comp_ae hgm hinv

theorem exercise_46_6_finite_measure_preserving_is_conservative
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → α} (hf : MeasurePreserving f μ μ) :
    Conservative f μ :=
  hf.conservative

end Book.Chapters.Chapter46
