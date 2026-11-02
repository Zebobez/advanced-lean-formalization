module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 40 — Markov Kernels and Transition Systems

Extracted from manuscript/chapters/part-06/chapter-40-markov-kernels-and-transition-systems.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter40

-- Source Lean fence 3

open Book.Models.FiniteTwoState

theorem transitionRowsHaveMassTwoAtZero : rowMass identityKernel zero = 2 :=
  identity_zero_row
theorem transitionRowsHaveMassTwoAtOne : rowMass identityKernel one = 2 :=
  identity_one_row

-- Source Lean fence 4
open MeasureTheory ProbabilityTheory

theorem exercise_40_2_markov_kernel_row_mass
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] (a : α) :
    κ a Set.univ = 1 := by
  simp

-- Source Lean fence 5
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem exercise_40_3_deterministic_kernel_map
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (μ : Measure α) :
    Kernel.deterministic f hf ∘ₘ μ = Measure.map f μ := by
  exact MeasureTheory.Measure.deterministic_comp_eq_map hf

-- Source Lean fence 6
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

theorem exercise_40_4_kernel_comp_apply
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ : Kernel α β) (η : Kernel β γ) (a : α) (s : Set γ)
    (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂κ a := by
  exact Kernel.comp_apply' η κ a hs

-- Source Lean fence 7
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem exercise_40_8_markov_kernel_comp
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ : Kernel α β) (η : Kernel β γ)
    [IsMarkovKernel κ] [IsMarkovKernel η] : IsMarkovKernel (η ∘ₖ κ) := by
  infer_instance

-- Source Lean fence 8
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem exercise_40_5_evolve_probability_measure
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (κ ∘ₘ μ) := by
  infer_instance

end Book.Chapters.Chapter40
