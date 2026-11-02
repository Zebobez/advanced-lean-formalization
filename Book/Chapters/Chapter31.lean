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
example {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (⋃ i, s i) := by
  exact MeasurableSet.iUnion hs

-- Source Lean fence 3
example {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {f : α → β} {g : β → γ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (g ∘ f) := by
  exact hg.comp hf

end Book.Chapters.Chapter31
