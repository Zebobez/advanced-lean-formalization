module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 38 — Martingale Convergence and Uniform Integrability

Extracted from manuscript/chapters/part-06/chapter-38-martingale-convergence.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter38

-- Source Lean fence 3

open Book.Models.FiniteTwoState

@[expose]
def conditionalPrediction (_time : Nat) : Int := 3

theorem predictionIsUniformlyIntegrableAtEveryFiniteTime (time : Nat) :
    conditionalPrediction time = 3 := rfl

-- Source Lean fence 4
open MeasureTheory
open Filter
open MeasureTheory.Filtration
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

theorem exercise_38_10_ae_tendsto_limitProcess
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m₀} {f : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    {R : ℝ≥0} (hf : Submartingale f ℱ μ)
    (hbounded : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) := by
  exact hf.ae_tendsto_limitProcess hbounded

-- Source Lean fence 5
open MeasureTheory
open Filter
open MeasureTheory.Filtration
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

theorem exercise_38_5_uniformIntegrable_l1_limit
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m₀} {f : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (huniform : UniformIntegrable f 1 μ) :
    Tendsto (fun n => eLpNorm (f n - ℱ.limitProcess f μ) 1 μ) atTop (𝓝 0) := by
  exact hf.tendsto_eLpNorm_one_limitProcess huniform

-- Source Lean fence 6
open MeasureTheory
open Filter
open MeasureTheory.Filtration
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

theorem exercise_38_5_martingale_limit_condExp
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m₀} {f : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hf : Martingale f ℱ μ) (huniform : UniformIntegrable f 1 μ) (n : ℕ) :
    f n =ᵐ[μ] μ[ℱ.limitProcess f μ | ℱ n] := by
  exact hf.ae_eq_condExp_limitProcess huniform n

-- Source Lean fence 7
open MeasureTheory
open Filter
open MeasureTheory.Filtration
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

theorem exercise_38_7_terminal_condExp_ae
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m₀} {g : Ω → ℝ} [IsFiniteMeasure μ]
    (hg : Integrable g μ) (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g | ℱ n]) x) atTop (𝓝 (g x)) := by
  exact hg.tendsto_ae_condExp hgmeas

-- Source Lean fence 8
open MeasureTheory
open Filter
open MeasureTheory.Filtration
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

theorem exercise_38_7_terminal_condExp_l1
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m₀} {g : Ω → ℝ} [IsFiniteMeasure μ]
    (hg : Integrable g μ) (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    Tendsto (fun n => eLpNorm (μ[g | ℱ n] - g) 1 μ) atTop (𝓝 0) := by
  exact hg.tendsto_eLpNorm_condExp hgmeas

end Book.Chapters.Chapter38
