module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 60 — Spectral Gaps and Continuous-Time Mixing

Extracted from manuscript/chapters/part-12/chapter-60-spectral-gaps-and-continuous-time-mixing.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter60

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def contrast : State → Int := fun s => if s = zero then 1 else -1
def flipActionAtZero : Int :=
  Int.ofNat (flipKernel zero zero) * contrast zero +
  Int.ofNat (flipKernel zero one) * contrast one

theorem flipNegatesTheContrast : flipActionAtZero = -2 := by decide

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def twoStateGeneratorQ (a b : ℚ) (i j : State) : ℚ :=
  if i = zero then (if j = zero then -a else a)
  else if j = zero then b else -b

def twoStateStationaryWeightQ (a b : ℚ) (i : State) : ℚ :=
  if i = zero then b / (a + b) else a / (a + b)

def twoStateActionQ (a b : ℚ) (f : State → ℚ) (i : State) : ℚ :=
  twoStateGeneratorQ a b i zero * f zero +
    twoStateGeneratorQ a b i one * f one

def twoStateMeanQ (a b : ℚ) (f : State → ℚ) : ℚ :=
  twoStateStationaryWeightQ a b zero * f zero +
    twoStateStationaryWeightQ a b one * f one

def twoStateCenterQ (a b : ℚ) (f : State → ℚ) (i : State) : ℚ :=
  f i - twoStateMeanQ a b f

def twoStateWeightedInnerQ (a b : ℚ) (f g : State → ℚ) : ℚ :=
  twoStateStationaryWeightQ a b zero * f zero * g zero +
    twoStateStationaryWeightQ a b one * f one * g one

theorem two_state_stationary_weight_total (a b : ℚ) (h : a + b ≠ 0) :
    twoStateStationaryWeightQ a b zero +
      twoStateStationaryWeightQ a b one = 1 := by
  simp [twoStateStationaryWeightQ, zero, one]; field_simp [h]; ring

theorem two_state_detailed_balance (a b : ℚ) :
    twoStateStationaryWeightQ a b zero * twoStateGeneratorQ a b zero one =
      twoStateStationaryWeightQ a b one * twoStateGeneratorQ a b one zero := by
  simp [twoStateStationaryWeightQ, twoStateGeneratorQ, zero, one]; ring

theorem two_state_generator_rows_sum_to_zero (a b : ℚ) (i : State) :
    twoStateGeneratorQ a b i zero + twoStateGeneratorQ a b i one = 0 := by
  fin_cases i
  · simp [twoStateGeneratorQ, zero, one]
  · simp [twoStateGeneratorQ, zero, one]

theorem two_state_stationary_mean_of_generator_action (a b : ℚ)
    (h : a + b ≠ 0) (f : State → ℚ) :
    twoStateMeanQ a b (twoStateActionQ a b f) = 0 := by
  simp [twoStateMeanQ, twoStateStationaryWeightQ, twoStateActionQ,
    twoStateGeneratorQ, zero, one]; field_simp [h]; ring

theorem two_state_center_has_mean_zero (a b : ℚ) (h : a + b ≠ 0)
    (f : State → ℚ) :
    twoStateMeanQ a b (twoStateCenterQ a b f) = 0 := by
  simp [twoStateMeanQ, twoStateCenterQ, twoStateStationaryWeightQ,
    zero, one]; field_simp [h]; ring

theorem two_state_centered_action_is_exact_eigenmode (a b : ℚ)
    (h : a + b ≠ 0) (f : State → ℚ) (i : State) :
    twoStateActionQ a b (twoStateCenterQ a b f) i =
      -(a + b) * twoStateCenterQ a b f i := by
  fin_cases i
  · simp [twoStateActionQ, twoStateGeneratorQ, twoStateCenterQ,
      twoStateMeanQ, twoStateStationaryWeightQ, zero, one]; field_simp [h]; ring
  · simp [twoStateActionQ, twoStateGeneratorQ, twoStateCenterQ,
      twoStateMeanQ, twoStateStationaryWeightQ, zero, one]; field_simp [h]; ring

theorem two_state_weighted_generator_self_adjoint (a b : ℚ)
    (h : a + b ≠ 0) (f g : State → ℚ) :
    twoStateWeightedInnerQ a b f (twoStateActionQ a b g) =
      twoStateWeightedInnerQ a b (twoStateActionQ a b f) g := by
  simp [twoStateWeightedInnerQ, twoStateStationaryWeightQ,
    twoStateActionQ, twoStateGeneratorQ, zero, one]; field_simp [h]; ring

end Book.Chapters.Chapter60
