module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 37 — Stopping Times and Optional Sampling

Extracted from manuscript/chapters/part-06/chapter-37-stopping-times-and-optional-sampling.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter37

-- Source Lean fence 3

open Book.Models.FiniteTwoState

def stoppedPosition : State → Nat := fun s => if s = zero then 0 else 1

theorem stopAtLowerState : stoppedPosition zero = 0 := by decide
theorem stopAtUpperState : stoppedPosition one = 1 := by decide

-- Source Lean fence 4
open MeasureTheory

theorem exercise_37_1_stopping_event_measurable
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (ℱ : Filtration ℕ m₀)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    MeasurableSet[ℱ n] {ω | τ ω ≤ n} := by
  exact hτ.measurableSet_le n

-- Source Lean fence 5
open MeasureTheory

theorem exercise_37_3_stoppedValue_const
    {Ω E : Type*} {f : ℕ → Ω → E} (N : ℕ) :
    MeasureTheory.stoppedValue f (fun _ => (N : WithTop ℕ)) = f N := by
  exact MeasureTheory.stoppedValue_const f N

-- Source Lean fence 6
open MeasureTheory
open scoped MeasureTheory ProbabilityTheory

theorem exercise_37_4_bounded_optional_sampling
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m₀} {f : ℕ → Ω → ℝ}
    [SigmaFiniteFiltration μ ℱ] (hf : Submartingale f ℱ μ)
    {τ π : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) (hπ : IsStoppingTime ℱ π) (hle : τ ≤ π)
    {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    μ[MeasureTheory.stoppedValue f τ] ≤ μ[MeasureTheory.stoppedValue f π] := by
  exact hf.expected_stoppedValue_mono hτ hπ hle hbdd

-- Source Lean fence 7
open MeasureTheory
open scoped MeasureTheory ProbabilityTheory

theorem exercise_37_10_optional_stopping_characterization
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m₀} {f : ℕ → Ω → ℝ}
    [SigmaFiniteFiltration μ ℱ]
    (hadapted : StronglyAdapted ℱ f) (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f ℱ μ ↔
      ∀ τ π : Ω → WithTop ℕ, IsStoppingTime ℱ τ → IsStoppingTime ℱ π →
        τ ≤ π → (∃ N : ℕ, ∀ ω, π ω ≤ N) →
          μ[MeasureTheory.stoppedValue f τ] ≤ μ[MeasureTheory.stoppedValue f π] := by
  exact submartingale_iff_expected_stoppedValue_mono hadapted hint

end Book.Chapters.Chapter37
