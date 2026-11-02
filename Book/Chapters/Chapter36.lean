module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 36 — Filtrations and Martingales

Extracted from manuscript/chapters/part-06/chapter-36-filtrations-and-martingales.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter36

-- Source Lean fence 3

open Book.Models.FiniteTwoState

def martingaleDifference : State → Int := fun s => if s = zero then -1 else 1

theorem fairDifferenceHasZeroMean :
    expectationNumerator uniformWeight martingaleDifference = 0 := by decide

-- Source Lean fence 4
open MeasureTheory

theorem exercise_36_1_filtration_mono
    {Ω ι : Type*} [Preorder ι] {m₀ : MeasurableSpace Ω}
    (ℱ : Filtration ι m₀) {i j : ι} (hij : i ≤ j) :
    ℱ i ≤ ℱ j := by
  exact ℱ.mono hij

-- Source Lean fence 5
open MeasureTheory

theorem exercise_36_3_martingale_condExp_identity
    {Ω E ι : Type*} [Preorder ι] {m₀ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {ℱ : Filtration ι m₀} {f : ι → Ω → E}
    (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    μ[f j | ℱ i] =ᵐ[μ] f i := by
  exact hf.2 i j hij

-- Source Lean fence 6
open MeasureTheory

theorem exercise_36_3_martingale_integrable
    {Ω E ι : Type*} [Preorder ι] {m₀ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {ℱ : Filtration ι m₀} {f : ι → Ω → E}
    (hf : Martingale f ℱ μ) (i : ι) : Integrable (f i) μ := by
  exact hf.integrable i

-- Source Lean fence 7
open MeasureTheory

theorem exercise_36_4_condExp_is_martingale
    {Ω E ι : Type*} [Preorder ι] {m₀ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : Ω → E) (ℱ : Filtration ι m₀) (μ : Measure Ω)
    [SigmaFiniteFiltration μ ℱ] :
    Martingale (fun i => μ[X | ℱ i]) ℱ μ := by
  exact martingale_condExp X ℱ μ

end Book.Chapters.Chapter36
