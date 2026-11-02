module

public import Mathlib

public section

/-!
# Chapter 33 — Product Measures and Fubini's Theorem

Extracted from manuscript/chapters/part-05/chapter-33-product-measures-and-fubini.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter33

-- Source Lean fence 2
open MeasureTheory

example {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  exact integral_prod f hf

end Book.Chapters.Chapter33
