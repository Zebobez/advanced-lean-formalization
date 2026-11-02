module

public import Book.Models.FiniteTwoState
public import Mathlib.Probability.Kernel.Posterior
public import Mathlib

public section

/-!
# Chapter 42 — Bayesian Updating and Posterior Kernels

Extracted from manuscript/chapters/part-06/chapter-42-bayesian-updating-and-posterior-kernels.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter42

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def prior : Weight := uniformWeight
def likelihood : Weight := fun s => if s = zero then 2 else 1
def posteriorWeight : Weight := fun s => prior s * likelihood s

theorem bayesNormalizer : totalWeight posteriorWeight = 3 := by decide
theorem posteriorFavorsZero : posteriorWeight zero = 2 := by decide

-- Source Lean fence 3

theorem exercise_42_1_binary_evidence :
    (1 / 3 : ℚ) * (3 / 4) + (2 / 3) * (1 / 4) = 5 / 12 := by
  norm_num

theorem exercise_42_2_binary_posterior :
    ((1 / 3 : ℚ) * (3 / 4)) / (5 / 12) = 3 / 5 := by
  norm_num

theorem exercise_42_3_binary_posterior_after_zero :
    ((1 / 3 : ℚ) * (1 / 4)) / (7 / 12) = 1 / 7 := by
  norm_num

-- Source Lean fence 4
open MeasureTheory ProbabilityTheory

theorem exercise_42_4_posterior_reconstruction
    {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (κ : Kernel Ω 𝓧) [IsFiniteKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    (κ ∘ₘ μ) ⊗ₘ posterior κ μ = (μ ⊗ₘ κ).map Prod.swap := by
  exact compProd_posterior_eq_map_swap

-- Source Lean fence 5
open MeasureTheory ProbabilityTheory

theorem exercise_42_5_posterior_is_markov
    {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (κ : Kernel Ω 𝓧) [IsFiniteKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    IsMarkovKernel (posterior κ μ) := by
  infer_instance

-- Source Lean fence 6
open MeasureTheory ProbabilityTheory

theorem exercise_42_6_posterior_candidate_unique
    {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (κ : Kernel Ω 𝓧) [IsFiniteKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (η : Kernel 𝓧 Ω) [IsFiniteKernel η]
    (h : (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap) :
    η =ᵐ[κ ∘ₘ μ] posterior κ μ := by
  exact ae_eq_posterior_of_compProd_eq h

-- Source Lean fence 7
open MeasureTheory ProbabilityTheory

theorem exercise_42_7_posterior_comp_self
    {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (κ : Kernel Ω 𝓧) [IsFiniteKernel κ] [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    posterior κ μ ∘ₘ κ ∘ₘ μ = μ := by
  exact posterior_comp_self

-- Source Lean fence 8
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem exercise_42_8_sequential_posterior_comp
    {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    [StandardBorelSpace Ω] [Nonempty Ω]
    [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (κ : Kernel Ω 𝓧) [IsFiniteKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (η : Kernel 𝓧 𝓨) [IsFiniteKernel η] :
    (η ∘ₖ κ)†μ =ᵐ[η ∘ₘ κ ∘ₘ μ] (κ†μ) ∘ₖ (η†(κ ∘ₘ μ)) := by
  exact posterior_comp

-- Source Lean fence 9
open MeasureTheory ProbabilityTheory

theorem exercise_42_9_deterministic_posterior_recovers_observation
    {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
    [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace.CountablyGenerated 𝓧]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → 𝓧) (hf : Measurable f) :
    Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ
      =ᵐ[μ.map f] Kernel.id := by
  exact deterministic_comp_posterior hf

end Book.Chapters.Chapter42
