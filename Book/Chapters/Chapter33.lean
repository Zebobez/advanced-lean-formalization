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

theorem exercise_33_3_fubini
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  exact integral_prod f hf

-- Source Lean fence 3
open MeasureTheory

theorem exercise_33_1_product_rectangle
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    (s : Set α) (t : Set β) :
    μ.prod ν (s ×ˢ t) = μ s * ν t := by
  simp

-- Source Lean fence 4
open MeasureTheory
open scoped ENNReal

theorem exercise_33_2_tonelli
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  exact lintegral_prod f hf

-- Source Lean fence 5
open MeasureTheory

theorem exercise_33_6_change_order
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ x, ∫ y, f (x, y) ∂ν ∂μ = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  exact integral_integral_swap hf

end Book.Chapters.Chapter33
