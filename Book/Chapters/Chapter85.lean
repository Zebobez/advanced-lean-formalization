module

public import Mathlib

public section

/-!
# Chapter 85 — Performance Measures from Matrix-Geometric Tails

Extracted from manuscript/chapters/part-22/chapter-85-performance-measures-from-matrix-geometric-tails.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter85

-- Source Lean fence 1
def phaseAInitialMass : ℚ := 3 / 8
def phaseBInitialMass : ℚ := 1 / 4
def phaseADecay : ℚ := 1 / 4
def phaseBDecay : ℚ := 1 / 2

def phaseATail (k : Nat) : ℚ := (1 / 2) * phaseADecay ^ k
def phaseBTail (k : Nat) : ℚ := (1 / 2) * phaseBDecay ^ k
def twoPhaseTail (k : Nat) : ℚ := phaseATail k + phaseBTail k

def phaseAMeanContribution : ℚ :=
  (1 / 2) * phaseADecay / (1 - phaseADecay)
def phaseBMeanContribution : ℚ :=
  (1 / 2) * phaseBDecay / (1 - phaseBDecay)
def twoPhaseMean : ℚ := phaseAMeanContribution + phaseBMeanContribution

def phaseASecondContribution : ℚ :=
  (1 / 2) * phaseADecay * (1 + phaseADecay) / (1 - phaseADecay) ^ 2
def phaseBSecondContribution : ℚ :=
  (1 / 2) * phaseBDecay * (1 + phaseBDecay) / (1 - phaseBDecay) ^ 2
def twoPhaseSecondMoment : ℚ := phaseASecondContribution + phaseBSecondContribution
def twoPhaseVariance : ℚ := twoPhaseSecondMoment - twoPhaseMean ^ 2

def twoPhasePGF (z : ℚ) : ℚ :=
  (3 / 8) / (1 - z / 4) + (1 / 4) / (1 - z / 2)

theorem phaseA_stationary_mass : phaseAInitialMass / (1 - phaseADecay) = 1 / 2 := by
  norm_num [phaseAInitialMass, phaseADecay]

theorem phaseB_stationary_mass : phaseBInitialMass / (1 - phaseBDecay) = 1 / 2 := by
  norm_num [phaseBInitialMass, phaseBDecay]

theorem twoPhase_total_mass :
    phaseAInitialMass / (1 - phaseADecay) +
      phaseBInitialMass / (1 - phaseBDecay) = 1 := by
  rw [phaseA_stationary_mass, phaseB_stationary_mass]
  norm_num

theorem phaseATail_succ (k : Nat) : phaseATail (k + 1) = phaseATail k / 4 := by
  unfold phaseATail phaseADecay
  rw [pow_succ]
  ring

theorem phaseBTail_succ (k : Nat) : phaseBTail (k + 1) = phaseBTail k / 2 := by
  unfold phaseBTail phaseBDecay
  rw [pow_succ]
  ring

theorem twoPhase_tail_at_three : twoPhaseTail 3 = 9 / 128 := by
  norm_num [twoPhaseTail, phaseATail, phaseBTail, phaseADecay, phaseBDecay]

theorem twoPhase_tail_ratios_differ :
    twoPhaseTail 1 / twoPhaseTail 0 ≠ twoPhaseTail 2 / twoPhaseTail 1 := by
  norm_num [twoPhaseTail, phaseATail, phaseBTail, phaseADecay, phaseBDecay]

theorem twoPhase_pgf_at_one : twoPhasePGF 1 = 1 := by
  norm_num [twoPhasePGF]

theorem phaseA_mean_is_one_sixth : phaseAMeanContribution = 1 / 6 := by
  norm_num [phaseAMeanContribution, phaseADecay]

theorem phaseB_mean_is_one_half : phaseBMeanContribution = 1 / 2 := by
  norm_num [phaseBMeanContribution, phaseBDecay]

theorem twoPhase_mean_is_two_thirds : twoPhaseMean = 2 / 3 := by
  rw [twoPhaseMean, phaseA_mean_is_one_sixth, phaseB_mean_is_one_half]
  norm_num

theorem phaseA_second_moment_is_five_eighteenths :
    phaseASecondContribution = 5 / 18 := by
  norm_num [phaseASecondContribution, phaseADecay]

theorem phaseB_second_moment_is_three_halves :
    phaseBSecondContribution = 3 / 2 := by
  norm_num [phaseBSecondContribution, phaseBDecay]

theorem twoPhase_second_moment_is_sixteen_ninths : twoPhaseSecondMoment = 16 / 9 := by
  rw [twoPhaseSecondMoment, phaseA_second_moment_is_five_eighteenths,
    phaseB_second_moment_is_three_halves]
  norm_num

theorem twoPhase_variance_is_four_thirds : twoPhaseVariance = 4 / 3 := by
  rw [twoPhaseVariance, twoPhase_second_moment_is_sixteen_ninths,
    twoPhase_mean_is_two_thirds]
  norm_num

end Book.Chapters.Chapter85
