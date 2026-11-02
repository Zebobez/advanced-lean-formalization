module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 35 — Conditional Expectation and Information

Extracted from manuscript/chapters/part-06/chapter-35-conditional-expectation.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter35

-- Source Lean fence 4

open Book.Models.FiniteTwoState

def eventMass : Weight := fun s => if s = zero then 1 else 0
def observedPayoff : State → Int := fun s => if s = zero then 0 else 2

theorem oneAtomPartition : totalWeight eventMass = 1 := by decide
theorem conditionalPayoffNumerator :
    expectationNumerator uniformWeight observedPayoff = 2 := by decide

-- Source Lean fence 5
open MeasureTheory

theorem exercise_35_1_condExp_measurable
    {α E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : α → E) :
    StronglyMeasurable[m] (MeasureTheory.condExp m μ f) := by
  exact MeasureTheory.stronglyMeasurable_condExp

-- Source Lean fence 6
open MeasureTheory

theorem exercise_35_1_condExp_integrable
    {α E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : α → E) : Integrable (MeasureTheory.condExp m μ f) μ := by
  exact MeasureTheory.integrable_condExp

-- Source Lean fence 7
open MeasureTheory

theorem exercise_35_1_condExp_setIntegral
    {α E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (f : α → E) (hf : Integrable f μ) (s : Set α) (hs : MeasurableSet[m] s) :
    ∫ x in s, (MeasureTheory.condExp m μ f) x ∂μ = ∫ x in s, f x ∂μ := by
  exact MeasureTheory.setIntegral_condExp hm hf hs

-- Source Lean fence 8
open MeasureTheory
open scoped ENNReal

theorem exercise_35_2_condExp_unique_ae
    {α E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {f g : α → E} (hf : Integrable f μ)
    (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ →
      ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
    (hgm : AEStronglyMeasurable[m] g μ) :
    g =ᵐ[μ] MeasureTheory.condExp m μ f := by
  exact MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hf hg_int_finite hg_eq hgm

-- Source Lean fence 9
open MeasureTheory

theorem exercise_35_7_condExp_of_measurable
    {α E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (f : α → E) (hf : StronglyMeasurable[m] f) (hfi : Integrable f μ) :
    MeasureTheory.condExp m μ f = f := by
  exact MeasureTheory.condExp_of_stronglyMeasurable hm hf hfi

-- Source Lean fence 10
open MeasureTheory

theorem exercise_35_5_tower
    {α E : Type*} {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure[m₀] α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim hm₂)]
    (f : α → E) :
    MeasureTheory.condExp m₁ μ (MeasureTheory.condExp m₂ μ f) =ᵐ[μ]
      MeasureTheory.condExp m₁ μ f := by
  exact MeasureTheory.condExp_condExp_of_le hm₁₂ hm₂

-- Source Lean fence 11
open MeasureTheory

theorem exercise_35_8_condExp_nonneg
    {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] MeasureTheory.condExp m μ f := by
  exact MeasureTheory.condExp_nonneg hf

end Book.Chapters.Chapter35
