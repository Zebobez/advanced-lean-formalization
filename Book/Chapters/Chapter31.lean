module

public import Mathlib

public section

/-!
# Chapter 31 — Measurable Functions and Almost-Everywhere Reasoning

Extracted from manuscript/chapters/part-05/chapter-31-measurable-functions-and-ae-reasoning.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter31

-- Source Lean fence 1
theorem exercise_31_2_countable_union_measurable
    {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (⋃ i, s i) := by
  exact MeasurableSet.iUnion hs

-- Source Lean fence 3
theorem exercise_31_1_measurable_comp
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {f : α → β} {g : β → γ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (g ∘ f) := by
  exact hg.comp hf

-- Source Lean fence 4
open MeasureTheory

-- Source Lean fence 5
theorem exercise_31_4_ae_eq_trans
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → β}
    (hfg : f =ᵐ[μ] g) (hgh : g =ᵐ[μ] h) : f =ᵐ[μ] h := by
  exact hfg.trans hgh

-- Source Lean fence 6
theorem exercise_31_6_measurable_ite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : MeasurableSet {x | p x})
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => if p x then f x else g x) := by
  exact Measurable.ite hp hf hg

end Book.Chapters.Chapter31
