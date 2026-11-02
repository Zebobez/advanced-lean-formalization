module

public import Book.Models.FiniteTwoState
public import Mathlib.Probability.Kernel.Irreducible
public import Mathlib

public section

/-!
# Chapter 44 — Irreducible Markov Kernels

Extracted from manuscript/chapters/part-06/chapter-44-irreducible-markov-kernels.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter44

-- Source Lean fence 2

open Book.Models.FiniteTwoState

theorem zeroCanReachOne : 0 < flipKernel zero one := by decide
theorem oneCanReachZero : 0 < flipKernel one zero := by decide

-- Source Lean fence 3

open MeasureTheory ProbabilityTheory

theorem measurableBoolNot : Measurable (fun b : Bool => !b) := by
  fun_prop

noncomputable def boolFlipKernel : Kernel Bool Bool :=
  Kernel.deterministic (fun b => !b) measurableBoolNot

theorem boolFlipKernel_irreducible :
    Kernel.IsIrreducible (Measure.count : Measure Bool) boolFlipKernel := by
  constructor
  intro A hA hφA a
  have hA_nonempty : A.Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero (μ := Measure.count) (ne_of_gt hφA)
  rcases hA_nonempty with ⟨b, hb⟩
  by_cases hab : a = b
  · subst b
    refine ⟨0, ?_⟩
    change 0 < Kernel.id a A
    rw [Kernel.id_apply, Measure.dirac_apply' _ hA]
    simp [hb]
  · have hflip : (!a) = b := by
      cases a <;> cases b <;> simp_all
    have hflip_mem : (!a) ∈ A := by simpa [hflip] using hb
    refine ⟨1, ?_⟩
    rw [pow_one, boolFlipKernel, Kernel.deterministic_apply' measurableBoolNot a hA]
    simp [hflip_mem]

-- Source Lean fence 4

open MeasureTheory ProbabilityTheory

theorem irreducible_of_smaller_reference_measure
    {α : Type*} [MeasurableSpace α] {φ₁ φ₂ : Measure α}
    (hφ : φ₁ ≤ φ₂) {κ : Kernel α α}
    [Kernel.IsIrreducible φ₂ κ] : Kernel.IsIrreducible φ₁ κ :=
  Kernel.isIrreducible_of_le_measure hφ

theorem zero_measure_is_irreducible
    {α : Type*} [MeasurableSpace α] (κ : Kernel α α) :
    Kernel.IsIrreducible (0 : Measure α) κ := by
  constructor
  intro A hA hφA a
  simp at hφA

end Book.Chapters.Chapter44
