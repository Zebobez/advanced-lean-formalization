module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 74 — Martingale Approximations for Additive Functionals

Extracted from manuscript/chapters/part-19/chapter-74-martingale-approximations-and-additive-functionals.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter74

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def additiveIncrement : State → Int := fun s => if s = zero then -1 else 1

theorem centeredAdditiveFunctional :
    expectationNumerator uniformWeight additiveIncrement = 0 := by decide

-- Source Lean fence 3
def symmetricGenerator (i j : State) : ℚ := if i = j then -1 else 1

def symmetricAction (f : State → ℚ) (i : State) : ℚ :=
  symmetricGenerator i zero * f zero + symmetricGenerator i one * f one

def carreDuChamp (f : State → ℚ) (i : State) : ℚ :=
  (f zero - f i) ^ 2 + (f one - f i) ^ 2

theorem carreDuChamp_identity (f : State → ℚ) (i : State) :
    carreDuChamp f i =
      symmetricAction (fun j => f j ^ 2) i -
        2 * f i * symmetricAction f i := by
  fin_cases i <;>
    simp [carreDuChamp, symmetricAction, symmetricGenerator, zero, one] <;>
    ring

theorem carreDuChamp_nonnegative (f : State → ℚ) (i : State) :
    0 ≤ carreDuChamp f i := by
  unfold carreDuChamp
  positivity

def twoStateCenteredObservable (i : State) : ℚ :=
  if i = zero then -1 else 1

def twoStatePoissonSolution (i : State) : ℚ :=
  if i = zero then -(1 / 2) else 1 / 2

def uniformStateMean (f : State → ℚ) : ℚ := (f zero + f one) / 2

theorem twoState_observable_centered :
    uniformStateMean twoStateCenteredObservable = 0 := by
  norm_num [uniformStateMean, twoStateCenteredObservable, zero, one]

theorem twoState_poisson_at_zero :
    symmetricAction twoStatePoissonSolution zero =
      -twoStateCenteredObservable zero := by
  norm_num [symmetricAction, symmetricGenerator, twoStatePoissonSolution,
    twoStateCenteredObservable, zero, one]

theorem twoState_poisson_at_one :
    symmetricAction twoStatePoissonSolution one =
      -twoStateCenteredObservable one := by
  norm_num [symmetricAction, symmetricGenerator, twoStatePoissonSolution,
    twoStateCenteredObservable, zero, one]

def bracketVariance : ℚ :=
  uniformStateMean (fun i => carreDuChamp twoStatePoissonSolution i)

def poissonVariance : ℚ :=
  2 * uniformStateMean
    (fun i => twoStatePoissonSolution i * twoStateCenteredObservable i)

theorem twoState_asymptotic_variance_identity :
    bracketVariance = poissonVariance := by
  norm_num [bracketVariance, poissonVariance, uniformStateMean,
    carreDuChamp, twoStatePoissonSolution, twoStateCenteredObservable,
    zero, one]

theorem twoState_asymptotic_variance_value : bracketVariance = 1 := by
  norm_num [bracketVariance, uniformStateMean, carreDuChamp,
    twoStatePoissonSolution, zero, one]

end Book.Chapters.Chapter74
