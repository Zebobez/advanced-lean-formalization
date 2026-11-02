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

example {α E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : PMF α) (f : α → E) (hf : Integrable f p.toMeasure) :
    ∫ a, f a ∂p.toMeasure = ∑' a, (p a).toReal • f a := by
  exact PMF.integral_eq_tsum p f hf

end Book.Chapters.Chapter34
