module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 54 — Resampling and Particle Systems

Extracted from manuscript/chapters/part-10/chapter-54-resampling-and-particle-systems.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter54

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def resampledCount : Weight := fun s => if s = zero then 2 else 0

theorem resamplingPreservesPopulationSize : totalWeight resampledCount = 2 := by decide
theorem allCopiesMayCoincide : resampledCount zero = 2 := by decide

-- Source Lean fence 2
def twoDrawAverage (x y : ℚ) (a b : Bool) : ℚ :=
  ((if a then y else x) + (if b then y else x)) / 2

theorem two_draw_resampling_unbiased (p x y : ℚ) :
    (1 - p) ^ 2 * twoDrawAverage x y false false +
      p * (1 - p) * twoDrawAverage x y false true +
      p * (1 - p) * twoDrawAverage x y true false +
      p ^ 2 * twoDrawAverage x y true true = (1 - p) * x + p * y := by
  simp [twoDrawAverage]
  ring

theorem two_draw_resampling_variance (p x y : ℚ) :
    (1 - p) ^ 2 * (twoDrawAverage x y false false - ((1 - p) * x + p * y)) ^ 2 +
      p * (1 - p) * (twoDrawAverage x y false true - ((1 - p) * x + p * y)) ^ 2 +
      p * (1 - p) * (twoDrawAverage x y true false - ((1 - p) * x + p * y)) ^ 2 +
      p ^ 2 * (twoDrawAverage x y true true - ((1 - p) * x + p * y)) ^ 2 =
        p * (1 - p) * (y - x) ^ 2 / 2 := by
  simp [twoDrawAverage]
  ring

-- Source Lean fence 3
def particleAncestorMass (b : Bool) : ℚ := if b then 3 / 4 else 1 / 4

def twoDrawMass (a b : Bool) : ℚ :=
  particleAncestorMass a * particleAncestorMass b

def resampledFraction (a b : Bool) : ℚ :=
  ((if a then 1 else 0) + (if b then 1 else 0)) / 2

def twoParticleExpectedFraction : ℚ :=
  twoDrawMass false false * resampledFraction false false +
    twoDrawMass false true * resampledFraction false true +
    twoDrawMass true false * resampledFraction true false +
    twoDrawMass true true * resampledFraction true true

def twoParticleResamplingVariance : ℚ :=
  twoDrawMass false false * (resampledFraction false false - 3 / 4) ^ 2 +
    twoDrawMass false true * (resampledFraction false true - 3 / 4) ^ 2 +
    twoDrawMass true false * (resampledFraction true false - 3 / 4) ^ 2 +
    twoDrawMass true true * (resampledFraction true true - 3 / 4) ^ 2

theorem two_particle_outcome_probabilities :
    twoDrawMass false false = 1 / 16 ∧
      twoDrawMass false true = 3 / 16 ∧
      twoDrawMass true false = 3 / 16 ∧
      twoDrawMass true true = 9 / 16 := by
  norm_num [twoDrawMass, particleAncestorMass]

theorem two_particle_resampling_is_unbiased :
    twoParticleExpectedFraction = 3 / 4 := by
  norm_num [twoParticleExpectedFraction, twoDrawMass, resampledFraction,
    particleAncestorMass]

theorem two_particle_resampling_variance :
    twoParticleResamplingVariance = 3 / 32 := by
  norm_num [twoParticleResamplingVariance, twoDrawMass, resampledFraction,
    particleAncestorMass]

theorem two_particle_duplicate_probability :
    twoDrawMass false false + twoDrawMass true true = 5 / 8 := by
  norm_num [twoDrawMass, particleAncestorMass]

-- Source Lean fence 4
def repeatedSlotState (i : Fin 3) : Bool := if i = 2 then false else true

def repeatedSlotMass (i : Fin 3) : ℚ := if i = 2 then 1 / 2 else 1 / 4

theorem first_two_slots_have_same_state :
    repeatedSlotState 0 = repeatedSlotState 1 := by decide

theorem repeated_state_weighted_mass :
    repeatedSlotMass 0 + repeatedSlotMass 1 = 1 / 2 := by
  norm_num [repeatedSlotMass]

end Book.Chapters.Chapter54
