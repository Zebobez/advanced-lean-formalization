module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 61 — Time-Inhomogeneous Chains and Evolution Families

Extracted from manuscript/chapters/part-13/chapter-61-time-inhomogeneous-chains-and-evolution-families.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter61

-- Source Lean fence 1

open Book.Models.FiniteTwoState

theorem identityThenFlipTransition : composeAt identityKernel flipKernel zero one = 2 := by decide
theorem flipThenIdentityTransition : composeAt flipKernel identityKernel zero one = 2 := by decide

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def rationalRowMassQ (k : State → State → ℚ) (i : State) : ℚ :=
  k i zero + k i one

def IsStochasticKernelQ (k : State → State → ℚ) : Prop :=
  (∀ i j, 0 ≤ k i j) ∧ (∀ i, rationalRowMassQ k i = 1)

def oneWayUpTransitionQ (p : ℚ) (i j : State) : ℚ :=
  if i = zero then (if j = zero then p else 1 - p)
  else if j = zero then 0 else 1

def oneWayDownTransitionQ (q : ℚ) (i j : State) : ℚ :=
  if i = zero then (if j = zero then 1 else 0)
  else if j = zero then 1 - q else q

def composeTransitionKernelQ (k l : State → State → ℚ)
    (i j : State) : ℚ :=
  k i zero * l zero j + k i one * l one j

theorem one_way_up_transition_stochastic (p : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsStochasticKernelQ (oneWayUpTransitionQ p) := by
  constructor
  · intro i j
    fin_cases i
    · fin_cases j
      · simpa [oneWayUpTransitionQ, zero, one] using hp0
      · have h : 0 ≤ 1 - p := by linarith
        simpa [oneWayUpTransitionQ, zero, one] using h
    · fin_cases j
      · norm_num [oneWayUpTransitionQ, zero, one]
      · norm_num [oneWayUpTransitionQ, zero, one]
  · intro i
    fin_cases i
    · dsimp [rationalRowMassQ, oneWayUpTransitionQ, zero, one]
      ring
    · norm_num [rationalRowMassQ, oneWayUpTransitionQ, zero, one]

theorem one_way_down_transition_stochastic (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsStochasticKernelQ (oneWayDownTransitionQ q) := by
  constructor
  · intro i j
    fin_cases i
    · fin_cases j
      · norm_num [oneWayDownTransitionQ, zero, one]
      · norm_num [oneWayDownTransitionQ, zero, one]
    · fin_cases j
      · have h : 0 ≤ 1 - q := by linarith
        simpa [oneWayDownTransitionQ, zero, one] using h
      · simpa [oneWayDownTransitionQ, zero, one] using hq0
  · intro i
    fin_cases i
    · norm_num [rationalRowMassQ, oneWayDownTransitionQ, zero, one]
    · dsimp [rationalRowMassQ, oneWayDownTransitionQ, zero, one]
      ring

theorem composition_preserves_row_mass (k l : State → State → ℚ)
    (hk : ∀ i, rationalRowMassQ k i = 1)
    (hl : ∀ i, rationalRowMassQ l i = 1) (i : State) :
    rationalRowMassQ (composeTransitionKernelQ k l) i = 1 := by
  calc
    rationalRowMassQ (composeTransitionKernelQ k l) i =
        k i zero * rationalRowMassQ l zero +
          k i one * rationalRowMassQ l one := by
      dsimp [rationalRowMassQ, composeTransitionKernelQ]
      ring
    _ = k i zero + k i one := by rw [hl zero, hl one]; ring
    _ = 1 := hk i

theorem composition_preserves_stochasticity (k l : State → State → ℚ)
    (hk : IsStochasticKernelQ k) (hl : IsStochasticKernelQ l) :
    IsStochasticKernelQ (composeTransitionKernelQ k l) := by
  constructor
  · intro i j
    exact add_nonneg
      (mul_nonneg (hk.1 i zero) (hl.1 zero j))
      (mul_nonneg (hk.1 i one) (hl.1 one j))
  · intro i
    exact composition_preserves_row_mass k l hk.2 hl.2 i

def one_way_up_then_down_Q (p q : ℚ) : State → State → ℚ :=
  composeTransitionKernelQ (oneWayUpTransitionQ p) (oneWayDownTransitionQ q)

def one_way_down_then_up_Q (p q : ℚ) : State → State → ℚ :=
  composeTransitionKernelQ (oneWayDownTransitionQ q) (oneWayUpTransitionQ p)

theorem one_way_up_then_down_upper_left (p q : ℚ) :
    one_way_up_then_down_Q p q zero zero = 1 - q + p * q := by
  simp [one_way_up_then_down_Q, composeTransitionKernelQ,
    oneWayUpTransitionQ, oneWayDownTransitionQ, zero, one]
  ring

theorem one_way_down_then_up_upper_left (p q : ℚ) :
    one_way_down_then_up_Q p q zero zero = p := by
  simp [one_way_down_then_up_Q, composeTransitionKernelQ,
    oneWayDownTransitionQ, oneWayUpTransitionQ, zero, one]

theorem one_way_phase_order_matters (p q : ℚ)
    (hp : p < 1) (hq : q < 1) :
    one_way_up_then_down_Q p q zero zero ≠
      one_way_down_then_up_Q p q zero zero := by
  rw [one_way_up_then_down_upper_left, one_way_down_then_up_upper_left]
  intro heq
  have hp' : 0 < 1 - p := by linarith
  have hq' : 0 < 1 - q := by linarith
  have hpos : 0 < (1 - p) * (1 - q) := mul_pos hp' hq'
  have hdiff : 1 - q + p * q - p = (1 - p) * (1 - q) := by ring
  have hzero : 1 - q + p * q - p = 0 := by linarith
  rw [hdiff] at hzero
  exact (ne_of_gt hpos) hzero

theorem one_way_phase_products_are_stochastic (p q : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsStochasticKernelQ (one_way_up_then_down_Q p q) ∧
      IsStochasticKernelQ (one_way_down_then_up_Q p q) := by
  constructor
  · exact composition_preserves_stochasticity _ _
      (one_way_up_transition_stochastic p hp0 hp1)
      (one_way_down_transition_stochastic q hq0 hq1)
  · exact composition_preserves_stochasticity _ _
      (one_way_down_transition_stochastic q hq0 hq1)
      (one_way_up_transition_stochastic p hp0 hp1)

end Book.Chapters.Chapter61
