module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 58 — Dynkin’s Formula and Generator Martingales

Extracted from manuscript/chapters/part-11/chapter-58-dynkins-formula-and-generator-martingales.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter58

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def stateIndicator : State → Int := fun s => if s = zero then 0 else 1

theorem generatorDriftAtZero :
    generatorAction twoStateGenerator stateIndicator zero = 1 := by decide

-- Source Lean fence 2
def rationalCTMCGenerator (a b : ℚ) (i j : State) : ℚ :=
  if i = zero then (if j = zero then -a else a)
  else if j = zero then b else -b

def rationalGeneratorAction (a b : ℚ) (f : State → ℚ) (i : State) : ℚ :=
  rationalCTMCGenerator a b i zero * f zero +
    rationalCTMCGenerator a b i one * f one

def indicatorOneQ (s : State) : ℚ := if s = one then 1 else 0

theorem indicator_one_drift_at_zero (a b : ℚ) :
    rationalGeneratorAction a b indicatorOneQ zero = a := by
  simp [rationalGeneratorAction, rationalCTMCGenerator, indicatorOneQ,
    zero, one]

theorem indicator_one_drift_at_one (a b : ℚ) :
    rationalGeneratorAction a b indicatorOneQ one = -b := by
  simp [rationalGeneratorAction, rationalCTMCGenerator, indicatorOneQ,
    zero, one]

theorem rational_generator_kills_constants (a b c : ℚ) (i : State) :
    rationalGeneratorAction a b (fun _ => c) i = 0 := by
  fin_cases i <;>
    simp [rationalGeneratorAction, rationalCTMCGenerator, zero, one]

-- Source Lean fence 3
def oneWayGenerator (d : ℚ) (i j : State) : ℚ :=
  if i = zero then 0 else if j = zero then d else -d

def oneWayGeneratorAction (d : ℚ) (f : State → ℚ) (i : State) : ℚ :=
  oneWayGenerator d i zero * f zero + oneWayGenerator d i one * f one

def oneWayAbsorptionPotential (d : ℚ) (i : State) : ℚ :=
  if i = zero then 0 else 1 / d

theorem one_way_absorption_potential_boundary (d : ℚ) :
    oneWayAbsorptionPotential d zero = 0 := by
  simp [oneWayAbsorptionPotential, zero]

theorem one_way_absorption_potential_solves_generator (d : ℚ) (hd : d ≠ 0) :
    oneWayGeneratorAction d (oneWayAbsorptionPotential d) one = -1 := by
  simp [oneWayGeneratorAction, oneWayGenerator, oneWayAbsorptionPotential,
    zero, one]
  field_simp [hd]

end Book.Chapters.Chapter58
