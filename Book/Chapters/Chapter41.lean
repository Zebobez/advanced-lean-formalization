module

public import Book.Models.FiniteTwoState
public import Mathlib.Probability.Kernel.Disintegration.Integral
public import Mathlib.Probability.Kernel.Disintegration.Unique
public import Mathlib

public section

/-!
# Chapter 41 — Disintegration and Conditional Kernels

Extracted from manuscript/chapters/part-06/chapter-41-disintegration-and-conditional-kernels.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter41

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def conditionalTable : Kernel := resetKernel
def observedMarginalAtZero : Nat := conditionalTable zero zero + conditionalTable one zero

theorem conditionalTableCell : conditionalTable zero one = 1 := by decide
theorem observedMarginal : observedMarginalAtZero = 2 := by decide

-- Source Lean fence 3
open MeasureTheory ProbabilityTheory

theorem exercise_41_1_disintegration_identity
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (ρ : Measure (α × Ω)) (ρCond : Kernel α Ω)
    [ρ.IsCondKernel ρCond] :
    ρ.fst ⊗ₘ ρCond = ρ := by
  exact ρ.disintegrate ρCond

-- Source Lean fence 4
open MeasureTheory ProbabilityTheory

theorem exercise_41_2_condKernel_reconstruction
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    ρ.fst ⊗ₘ ρ.condKernel = ρ := by
  exact ρ.disintegrate ρ.condKernel

-- Source Lean fence 5
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem exercise_41_3_condKernel_atom_formula
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [MeasurableSingletonClass α] [StandardBorelSpace Ω] [Nonempty Ω]
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] {a : α}
    (ha : ρ.fst {a} ≠ 0) (s : Set Ω) :
    ρ.condKernel a s = (ρ.fst {a})⁻¹ * ρ ({a} ×ˢ s) := by
  exact Measure.condKernel_apply_of_ne_zero ha s

-- Source Lean fence 6
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem exercise_41_4_lintegral_disintegration
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]
    (f : α × Ω → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ a, ∫⁻ ω, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫⁻ p, f p ∂ρ := by
  exact ρ.lintegral_condKernel hf

-- Source Lean fence 7
open MeasureTheory ProbabilityTheory

theorem exercise_41_5_conditional_kernel_ae_unique
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α Ω) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).condKernel =ᵐ[μ] κ := by
  exact ProbabilityTheory.condKernel_compProd μ κ

-- Source Lean fence 8
open MeasureTheory ProbabilityTheory

theorem exercise_41_6_deterministic_conditional_law
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure α) [IsFiniteMeasure μ] (g : α → Ω) (hg : Measurable g) :
    (μ ⊗ₘ Kernel.deterministic g hg).condKernel =ᵐ[μ]
      Kernel.deterministic g hg := by
  exact ProbabilityTheory.condKernel_compProd μ (Kernel.deterministic g hg)

end Book.Chapters.Chapter41
