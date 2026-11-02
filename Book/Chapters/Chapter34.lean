module

public import Mathlib

public section

/-!
# Chapter 34 — Probability Measures and Random Variables

Extracted from manuscript/chapters/part-06/chapter-34-probability-and-random-variables.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter34

-- Source Lean fence 2
open MeasureTheory

theorem exercise_34_3_pmf_expectation
    {α E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : PMF α) (f : α → E) (hf : Integrable f p.toMeasure) :
    ∫ a, f a ∂p.toMeasure = ∑' a, (p a).toReal • f a := by
  exact PMF.integral_eq_tsum p f hf

-- Source Lean fence 3
open MeasureTheory

theorem exercise_34_1_probability_univ
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    P Set.univ = 1 := by
  simp

-- Source Lean fence 4
open MeasureTheory

theorem exercise_34_2_law_preimage
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (s : Set E) (hs : MeasurableSet s) :
    Measure.map X P s = P (X ⁻¹' s) := by
  exact Measure.map_apply hX hs

-- Source Lean fence 5
open MeasureTheory

theorem exercise_34_4_indepFun_events
    {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    (P : Measure Ω) (X : Ω → E) (Y : Ω → F) :
    ProbabilityTheory.IndepFun X Y P ↔
      ∀ s t, MeasurableSet s → MeasurableSet t →
        P (X ⁻¹' s ∩ Y ⁻¹' t) = P (X ⁻¹' s) * P (Y ⁻¹' t) := by
  exact ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul

end Book.Chapters.Chapter34
