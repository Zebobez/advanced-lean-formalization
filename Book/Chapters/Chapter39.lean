module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 39 — Predictable Processes and Doob Decomposition

Extracted from manuscript/chapters/part-06/chapter-39-predictable-processes-and-doob-decomposition.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter39

-- Source Lean fence 3

open Book.Models.FiniteTwoState

def rawIncrement : State → Int := fun s => if s = zero then -1 else 1
def predictableDrift : State → Int := rawIncrement
def martingaleResidual (s : State) : Int := rawIncrement s - predictableDrift s

theorem residualAtZero : martingaleResidual zero = 0 := by decide
theorem residualAtOne : martingaleResidual one = 0 := by decide

-- Source Lean fence 4
open MeasureTheory
open scoped MeasureTheory ProbabilityTheory

theorem exercise_39_3_predictablePart_recurrence
    {Ω E : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℱ : Filtration ℕ m₀) (f : ℕ → Ω → E) (n : ℕ) :
    predictablePart f ℱ μ (n + 1) =
      predictablePart f ℱ μ n + μ[f (n + 1) - f n | ℱ n] := by
  exact predictablePart_add_one n

-- Source Lean fence 5
open MeasureTheory

theorem exercise_39_8_doob_decomposition_identity
    {Ω E : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℱ : Filtration ℕ m₀) (f : ℕ → Ω → E) :
    martingalePart f ℱ μ + predictablePart f ℱ μ = f := by
  exact martingalePart_add_predictablePart ℱ μ f

-- Source Lean fence 6
open MeasureTheory

theorem exercise_39_8_martingalePart_is_martingale
    {Ω E : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ℱ : Filtration ℕ m₀) (f : ℕ → Ω → E)
    (hadapted : StronglyAdapted ℱ f) (hint : ∀ n, Integrable (f n) μ)
    [SigmaFiniteFiltration μ ℱ] :
    Martingale (martingalePart f ℱ μ) ℱ μ := by
  exact martingale_martingalePart hadapted hint

-- Source Lean fence 7
open MeasureTheory

theorem exercise_39_7_predictablePart_of_martingale
    {Ω E : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ℱ : Filtration ℕ m₀} {f : ℕ → Ω → E}
    (hf : Martingale f ℱ μ) (n : ℕ) :
    predictablePart f ℱ μ n =ᵐ[μ] (0 : Ω → E) := by
  exact hf.predictablePart_eq_zero n

end Book.Chapters.Chapter39
