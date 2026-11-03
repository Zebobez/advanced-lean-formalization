module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 55 — Finite-State Continuous-Time Markov Chains

Extracted from manuscript/chapters/part-11/chapter-55-finite-state-continuous-time-markov-chains.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter55

-- Source Lean fence 2

open Book.Models.FiniteTwoState

theorem generatorConservesMassAtZero : generatorRowSum twoStateGenerator zero = 0 :=
  generator_zero_row
theorem generatorConservesMassAtOne : generatorRowSum twoStateGenerator one = 0 :=
  generator_one_row

-- Source Lean fence 3
def rationalTwoStateGenerator (a b : ℚ) (i j : State) : ℚ :=
  if i = zero then (if j = zero then -a else a)
  else if j = zero then b else -b

def rationalTwoStateRowSum (a b : ℚ) (i : State) : ℚ :=
  rationalTwoStateGenerator a b i zero + rationalTwoStateGenerator a b i one

def rationalTwoStateStationary (a b : ℚ) (i : State) : ℚ :=
  if i = zero then b / (a + b) else a / (a + b)

def rationalTwoStateStationaryAction (a b : ℚ) (j : State) : ℚ :=
  rationalTwoStateStationary a b zero * rationalTwoStateGenerator a b zero j +
    rationalTwoStateStationary a b one * rationalTwoStateGenerator a b one j

theorem rational_two_state_generator_row_sum (a b : ℚ) (i : State) :
    rationalTwoStateRowSum a b i = 0 := by
  fin_cases i <;>
    simp [rationalTwoStateRowSum, rationalTwoStateGenerator, zero, one]

theorem rational_two_state_stationary_normalized (a b : ℚ) (h : a + b ≠ 0) :
    rationalTwoStateStationary a b zero + rationalTwoStateStationary a b one = 1 := by
  simp [rationalTwoStateStationary, zero, one]
  field_simp [h]
  exact add_comm b a

theorem rational_two_state_stationary_equation (a b : ℚ) (h : a + b ≠ 0)
    (j : State) : rationalTwoStateStationaryAction a b j = 0 := by
  fin_cases j <;>
    simp [rationalTwoStateStationaryAction, rationalTwoStateStationary,
      rationalTwoStateGenerator, zero, one] <;>
    field_simp [h] <;> ring

-- Source Lean fence 4
def threeCycleGenerator (c : ℚ) (i j : Fin 3) : ℚ :=
  if i = 0 then (if j = 0 then -c else if j = 1 then c else 0)
  else if i = 1 then (if j = 1 then -c else if j = 2 then c else 0)
  else if j = 0 then c else if j = 2 then -c else 0

def threeCycleRowSum (c : ℚ) (i : Fin 3) : ℚ :=
  threeCycleGenerator c i 0 + threeCycleGenerator c i 1 + threeCycleGenerator c i 2

def threeCycleColumnSum (c : ℚ) (j : Fin 3) : ℚ :=
  threeCycleGenerator c 0 j + threeCycleGenerator c 1 j + threeCycleGenerator c 2 j

theorem three_cycle_rows_sum_to_zero (c : ℚ) (i : Fin 3) :
    threeCycleRowSum c i = 0 := by
  fin_cases i <;> simp [threeCycleRowSum, threeCycleGenerator]

theorem three_cycle_uniform_stationary (c : ℚ) (j : Fin 3) :
    (1 / 3 : ℚ) * threeCycleGenerator c 0 j +
      (1 / 3 : ℚ) * threeCycleGenerator c 1 j +
      (1 / 3 : ℚ) * threeCycleGenerator c 2 j = 0 := by
  fin_cases j <;> simp [threeCycleGenerator]

theorem three_cycle_uniform_mass :
    (1 / 3 : ℚ) + 1 / 3 + 1 / 3 = 1 := by norm_num

theorem three_cycle_edge_flows_differ (c : ℚ) (hc : 0 < c) :
    (1 / 3 : ℚ) * threeCycleGenerator c 0 1 ≠
      (1 / 3 : ℚ) * threeCycleGenerator c 1 0 := by
  simp [threeCycleGenerator]
  positivity

end Book.Chapters.Chapter55
