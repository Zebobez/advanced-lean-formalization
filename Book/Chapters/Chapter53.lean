module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 53 — Sequential Importance Sampling and Filtering

Extracted from manuscript/chapters/part-10/chapter-53-sequential-importance-sampling-and-filtering.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter53

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def firstLikelihood : Weight := fun s => if s = zero then 2 else 1
def secondLikelihood : Weight := fun _ => 1
def sequentialWeight : Weight := fun s => firstLikelihood s * secondLikelihood s

theorem oneStepFilterNormalizer : totalWeight sequentialWeight = 3 := by decide

-- Source Lean fence 3
def binaryUniformPrior : Bool → ℚ := fun _ => 1 / 2

def binaryObservationLikelihood : Bool → ℚ := fun b =>
  if b then 3 / 4 else 1 / 4

def binarySwitchKernel (r : ℚ) (x z : Bool) : ℚ :=
  if x = z then 1 - r else r

def binaryPredict (μ : Bool → ℚ) (r : ℚ) (z : Bool) : ℚ :=
  μ false * binarySwitchKernel r false z +
    μ true * binarySwitchKernel r true z

def binaryEvidence (μ G : Bool → ℚ) : ℚ :=
  μ false * G false + μ true * G true

def binaryUpdate (μ G : Bool → ℚ) (z : Bool) : ℚ :=
  μ z * G z / binaryEvidence μ G

theorem binary_uniform_prediction (r : ℚ) (z : Bool) :
    binaryPredict binaryUniformPrior r z = 1 / 2 := by
  cases z <;> simp [binaryPredict, binaryUniformPrior, binarySwitchKernel] <;> ring

theorem binary_first_evidence :
    binaryEvidence binaryUniformPrior binaryObservationLikelihood = 1 / 2 := by
  norm_num [binaryEvidence, binaryUniformPrior, binaryObservationLikelihood]

theorem binary_first_posterior_true :
    binaryUpdate binaryUniformPrior binaryObservationLikelihood true = 3 / 4 := by
  norm_num [binaryUpdate, binaryEvidence, binaryUniformPrior,
    binaryObservationLikelihood]

theorem binary_first_posterior_false :
    binaryUpdate binaryUniformPrior binaryObservationLikelihood false = 1 / 4 := by
  norm_num [binaryUpdate, binaryEvidence, binaryUniformPrior,
    binaryObservationLikelihood]

-- Source Lean fence 4
def binaryFirstFilter (z : Bool) : ℚ :=
  binaryUpdate binaryUniformPrior binaryObservationLikelihood z

def binarySecondPrediction (z : Bool) : ℚ :=
  binaryPredict binaryFirstFilter (1 / 4) z

def binarySecondEvidence : ℚ :=
  binaryEvidence binarySecondPrediction binaryObservationLikelihood

def binarySecondFilter (z : Bool) : ℚ :=
  binaryUpdate binarySecondPrediction binaryObservationLikelihood z

theorem binary_second_prediction_false :
    binarySecondPrediction false = 3 / 8 := by
  norm_num [binarySecondPrediction, binaryPredict, binaryFirstFilter,
    binaryUpdate, binaryEvidence, binaryUniformPrior,
    binaryObservationLikelihood, binarySwitchKernel]

theorem binary_second_prediction_true :
    binarySecondPrediction true = 5 / 8 := by
  norm_num [binarySecondPrediction, binaryPredict, binaryFirstFilter,
    binaryUpdate, binaryEvidence, binaryUniformPrior,
    binaryObservationLikelihood, binarySwitchKernel]

theorem binary_second_evidence : binarySecondEvidence = 9 / 16 := by
  norm_num [binarySecondEvidence, binaryEvidence, binarySecondPrediction,
    binaryPredict, binaryFirstFilter, binaryUpdate, binaryUniformPrior,
    binaryObservationLikelihood, binarySwitchKernel]

theorem binary_second_posterior_true : binarySecondFilter true = 5 / 6 := by
  norm_num [binarySecondFilter, binaryUpdate, binarySecondEvidence,
    binaryEvidence, binarySecondPrediction, binaryPredict, binaryFirstFilter,
    binaryUniformPrior, binaryObservationLikelihood, binarySwitchKernel]

theorem binary_two_step_evidence :
    (1 / 2 : ℚ) * binarySecondEvidence = 9 / 32 := by
  norm_num [binarySecondEvidence, binaryEvidence, binarySecondPrediction,
    binaryPredict, binaryFirstFilter, binaryUpdate, binaryUniformPrior,
    binaryObservationLikelihood, binarySwitchKernel]

-- Source Lean fence 5
theorem sequential_path_weight_cancels
    (η q₀ r₁ r₂ m₁ m₂ g₁ g₂ : ℚ)
    (hq : q₀ ≠ 0) (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) :
    q₀ * r₁ * r₂ *
      ((η / q₀) * (g₁ * (m₁ / r₁)) * (g₂ * (m₂ / r₂))) =
        η * m₁ * g₁ * m₂ * g₂ := by
  field_simp [hq, hr₁, hr₂]

end Book.Chapters.Chapter53
