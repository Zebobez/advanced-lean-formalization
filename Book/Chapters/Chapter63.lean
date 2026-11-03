module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 63 — Birth–Death Chains and Hitting Problems

Extracted from manuscript/chapters/part-14/chapter-63-birth-death-chains-and-hitting-problems.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter63

-- Source Lean fence 2

open Book.Models.FiniteTwoState

theorem birthRateFromZero : twoStateGenerator zero one = 1 := by decide
theorem deathRateFromOne : twoStateGenerator one zero = 2 := by decide
theorem birthDeathRowBalance :
    generatorRowSum twoStateGenerator zero = 0 := generator_zero_row

-- Source Lean fence 3

open Book.Models.FiniteTwoState

def threeStateBirthDeathGeneratorQ (a b : ℚ) (i j : Fin 3) : ℚ :=
  if i = 0 then (if j = 0 then -a else if j = 1 then a else 0)
  else if i = 1 then
    (if j = 0 then b else if j = 1 then -(a + b) else a)
  else if j = 1 then b else if j = 2 then -b else 0

def threeStateBirthDeathActionQ (a b : ℚ) (f : Fin 3 → ℚ)
    (i : Fin 3) : ℚ :=
  threeStateBirthDeathGeneratorQ a b i 0 * f 0 +
    threeStateBirthDeathGeneratorQ a b i 1 * f 1 +
    threeStateBirthDeathGeneratorQ a b i 2 * f 2

def threeStateHittingProbabilityQ (a b : ℚ) (i : Fin 3) : ℚ :=
  if i = 0 then 0 else if i = 1 then a / (a + b) else 1

def threeStateExpectedTimeQ (a b : ℚ) (i : Fin 3) : ℚ :=
  if i = 1 then 1 / (a + b) else 0

theorem three_state_hitting_probability_boundary_values (a b : ℚ) :
    threeStateHittingProbabilityQ a b 0 = 0 ∧
      threeStateHittingProbabilityQ a b 2 = 1 := by
  simp [threeStateHittingProbabilityQ]

theorem three_state_hitting_probability_harmonic (a b : ℚ)
    (h : a + b ≠ 0) :
    threeStateBirthDeathActionQ a b (threeStateHittingProbabilityQ a b) 1 = 0 := by
  simp [threeStateBirthDeathActionQ, threeStateBirthDeathGeneratorQ,
    threeStateHittingProbabilityQ]
  field_simp [h]
  ring

theorem three_state_harmonic_solution_unique (a b : ℚ)
    (h : a + b ≠ 0) (f : Fin 3 → ℚ)
    (h0 : f 0 = 0) (h2 : f 2 = 1)
    (hharmonic : threeStateBirthDeathActionQ a b f 1 = 0) :
    f 1 = a / (a + b) := by
  have hform : b * f 0 - (a + b) * f 1 + a * f 2 = 0 := by
    have hh := hharmonic
    simp [threeStateBirthDeathActionQ, threeStateBirthDeathGeneratorQ] at hh
    nlinarith [hh]
  rw [h0, h2] at hform
  field_simp [h] at hform ⊢
  nlinarith

theorem three_state_expected_time_boundary_values (a b : ℚ) :
    threeStateExpectedTimeQ a b 0 = 0 ∧
      threeStateExpectedTimeQ a b 2 = 0 := by
  simp [threeStateExpectedTimeQ]

theorem three_state_expected_time_poisson_equation (a b : ℚ)
    (h : a + b ≠ 0) :
    threeStateBirthDeathActionQ a b (threeStateExpectedTimeQ a b) 1 = -1 := by
  simp [threeStateBirthDeathActionQ, threeStateBirthDeathGeneratorQ,
    threeStateExpectedTimeQ]
  field_simp [h]
  ring

theorem three_state_poisson_solution_unique (a b : ℚ)
    (h : a + b ≠ 0) (f : Fin 3 → ℚ)
    (h0 : f 0 = 0) (h2 : f 2 = 0)
    (hpoisson : threeStateBirthDeathActionQ a b f 1 = -1) :
    f 1 = 1 / (a + b) := by
  have hform : b * f 0 - (a + b) * f 1 + a * f 2 = -1 := by
    have hp := hpoisson
    simp [threeStateBirthDeathActionQ, threeStateBirthDeathGeneratorQ] at hp
    nlinarith [hp]
  rw [h0, h2] at hform
  field_simp [h] at hform ⊢
  nlinarith

end Book.Chapters.Chapter63
