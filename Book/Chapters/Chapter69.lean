module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 69 — Linear Response for Finite Markov Chains

Extracted from manuscript/chapters/part-16/chapter-69-linear-response-for-finite-markov-chains.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter69

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def stationaryMass (parameter : Nat) : Nat := parameter + 1
def finiteResponse (base perturbation : Nat) : Nat :=
  stationaryMass (base + perturbation) - stationaryMass base

theorem unitPerturbationResponse : finiteResponse 1 1 = 1 := by decide

-- Source Lean fence 3
def responsePiZero (a b : ℚ) : ℚ := b / (a + b)
def responsePiOne (a b : ℚ) : ℚ := a / (a + b)

def poissonHZero (a b : ℚ) : ℚ := -a / (a + b) ^ 2
def poissonHOne (a b : ℚ) : ℚ := b / (a + b) ^ 2

theorem poisson_gap (a b : ℚ) (hab : a + b ≠ 0) :
    poissonHOne a b - poissonHZero a b = 1 / (a + b) := by
  unfold poissonHOne poissonHZero
  field_simp [hab]
  ring

theorem poisson_centered (a b : ℚ) (hab : a + b ≠ 0) :
    responsePiZero a b * poissonHZero a b +
      responsePiOne a b * poissonHOne a b = 0 := by
  unfold responsePiZero responsePiOne poissonHZero poissonHOne
  field_simp [hab]
  ring

theorem poisson_equation_state_zero (a b : ℚ) (hab : a + b ≠ 0) :
    a * (poissonHOne a b - poissonHZero a b) = a / (a + b) := by
  unfold poissonHOne poissonHZero
  field_simp [hab]
  ring

theorem poisson_equation_state_one (a b : ℚ) (hab : a + b ≠ 0) :
    b * (poissonHZero a b - poissonHOne a b) = -b / (a + b) := by
  unfold poissonHOne poissonHZero
  field_simp [hab]
  ring

def responseFromPoisson (a b da db : ℚ) : ℚ :=
  responsePiZero a b * da * (poissonHOne a b - poissonHZero a b) +
    responsePiOne a b * db * (poissonHZero a b - poissonHOne a b)

def responseClosedForm (a b da db : ℚ) : ℚ :=
  (b * da - a * db) / (a + b) ^ 2

theorem twoState_linear_response (a b da db : ℚ) (hab : a + b ≠ 0) :
    responseFromPoisson a b da db = responseClosedForm a b da db := by
  unfold responseFromPoisson responseClosedForm
    responsePiZero responsePiOne poissonHZero poissonHOne
  field_simp [hab]
  ring

end Book.Chapters.Chapter69
