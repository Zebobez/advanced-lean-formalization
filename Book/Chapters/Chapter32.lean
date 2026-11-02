module

public import Mathlib

public section

/-!
# Chapter 32 — Bochner Integration and Convergence Theorems

Extracted from manuscript/chapters/part-05/chapter-32-bochner-integration-and-convergence.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter32

-- Source Lean fence 2
open MeasureTheory

example {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f g : α → E) (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = (∫ x, f x ∂μ) + ∫ x, g x ∂μ := by
  exact integral_add hf hg

-- Source Lean fence 3
open MeasureTheory

example {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : α → E} (h : f =ᵐ[μ] g) :
    ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  exact integral_congr_ae h

end Book.Chapters.Chapter32
