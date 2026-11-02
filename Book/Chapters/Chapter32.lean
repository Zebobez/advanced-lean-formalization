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

theorem exercise_32_1_integral_add
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f g : α → E) (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = (∫ x, f x ∂μ) + ∫ x, g x ∂μ := by
  exact integral_add hf hg

-- Source Lean fence 3
open MeasureTheory

theorem exercise_32_2_integral_congr_ae
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : α → E} (h : f =ᵐ[μ] g) :
    ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  exact integral_congr_ae h

-- Source Lean fence 5
open MeasureTheory

-- Source Lean fence 6
theorem exercise_32_3_norm_integral_le_integral_norm
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : α → E) :
    ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  exact norm_integral_le_integral_norm f

-- Source Lean fence 7
theorem exercise_32_7_continuous_linear_map_integral
    {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : α → E) (L : E →L[ℝ] F) (hf : Integrable f μ) :
    ∫ x, L (f x) ∂μ = L (∫ x, f x ∂μ) := by
  exact L.integral_comp_comm hf

end Book.Chapters.Chapter32
