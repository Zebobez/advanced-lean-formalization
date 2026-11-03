module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 62 — Coupling and Continuous-Time Mixing

Extracted from manuscript/chapters/part-13/chapter-62-coupling-and-continuous-time-mixing.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter62

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def flipState (s : State) : State := if s = zero then one else zero
def synchronousFlip (p : State × State) : State × State :=
  (flipState p.1, flipState p.2)

theorem diagonalCouplingStaysDiagonal :
    synchronousFlip (zero, zero) = (one, one) := by decide

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def bernoulliProbabilityQ (p : ℚ) (x : State) : ℚ :=
  if x = zero then p else 1 - p

def maximalBernoulliCouplingQ (p q : ℚ) (x y : State) : ℚ :=
  if p ≤ q then
    if x = zero then (if y = zero then p else 0)
    else if y = zero then q - p else 1 - q
  else
    if x = zero then (if y = zero then q else p - q)
    else if y = zero then 0 else 1 - p

def maximalCouplingFirstMarginalQ (p q : ℚ) (x : State) : ℚ :=
  maximalBernoulliCouplingQ p q x zero +
    maximalBernoulliCouplingQ p q x one

def maximalCouplingSecondMarginalQ (p q : ℚ) (y : State) : ℚ :=
  maximalBernoulliCouplingQ p q zero y +
    maximalBernoulliCouplingQ p q one y

def maximalCouplingMassQ (p q : ℚ) : ℚ :=
  maximalCouplingFirstMarginalQ p q zero +
    maximalCouplingFirstMarginalQ p q one

def maximalCouplingMismatchQ (p q : ℚ) : ℚ :=
  maximalBernoulliCouplingQ p q zero one +
    maximalBernoulliCouplingQ p q one zero

def bernoulliTotalVariationQ (p q : ℚ) : ℚ :=
  (|p - q| + |(1 - p) - (1 - q)|) / 2

theorem maximal_coupling_first_marginal (p q : ℚ) (x : State) :
    maximalCouplingFirstMarginalQ p q x = bernoulliProbabilityQ p x := by
  fin_cases x
  · by_cases h : p ≤ q
    · simp [maximalCouplingFirstMarginalQ, maximalBernoulliCouplingQ,
        bernoulliProbabilityQ, h, zero, one]
    · simp [maximalCouplingFirstMarginalQ, maximalBernoulliCouplingQ,
        bernoulliProbabilityQ, h, zero, one]
  · by_cases h : p ≤ q
    · simp [maximalCouplingFirstMarginalQ, maximalBernoulliCouplingQ,
        bernoulliProbabilityQ, h, zero, one]
    · simp [maximalCouplingFirstMarginalQ, maximalBernoulliCouplingQ,
        bernoulliProbabilityQ, h, zero, one]

theorem maximal_coupling_second_marginal (p q : ℚ) (y : State) :
    maximalCouplingSecondMarginalQ p q y = bernoulliProbabilityQ q y := by
  fin_cases y
  · by_cases h : p ≤ q
    · simp [maximalCouplingSecondMarginalQ, maximalBernoulliCouplingQ,
        bernoulliProbabilityQ, h, zero, one]
    · simp [maximalCouplingSecondMarginalQ, maximalBernoulliCouplingQ,
        bernoulliProbabilityQ, h, zero, one]
  · by_cases h : p ≤ q
    · simp [maximalCouplingSecondMarginalQ, maximalBernoulliCouplingQ,
        bernoulliProbabilityQ, h, zero, one]
    · simp [maximalCouplingSecondMarginalQ, maximalBernoulliCouplingQ,
        bernoulliProbabilityQ, h, zero, one]

theorem maximal_coupling_total_mass (p q : ℚ) :
    maximalCouplingMassQ p q = 1 := by
  rw [maximalCouplingMassQ, maximal_coupling_first_marginal p q zero,
    maximal_coupling_first_marginal p q one]
  simp [bernoulliProbabilityQ, zero, one]

theorem maximal_coupling_entries_nonnegative (p q : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (x y : State) : 0 ≤ maximalBernoulliCouplingQ p q x y := by
  by_cases h : p ≤ q
  · fin_cases x
    · fin_cases y
      · simpa [maximalBernoulliCouplingQ, h, zero, one] using hp0
      · norm_num [maximalBernoulliCouplingQ, h, zero, one]
    · fin_cases y
      · simp [maximalBernoulliCouplingQ, h, zero]
      · have hdiff : 0 ≤ 1 - q := by linarith
        simp [maximalBernoulliCouplingQ, h, zero]
        linarith
  · have hqp : q < p := lt_of_not_ge h
    fin_cases x
    · fin_cases y
      · simpa [maximalBernoulliCouplingQ, h, zero, one] using hq0
      · have hdiff : 0 ≤ p - q := sub_nonneg.mpr (le_of_lt hqp)
        simp [maximalBernoulliCouplingQ, h, zero]
        linarith
    · fin_cases y
      · norm_num [maximalBernoulliCouplingQ, h, zero, one]
      · have hdiff : 0 ≤ 1 - p := by linarith
        simp [maximalBernoulliCouplingQ, h, zero]
        linarith

theorem maximal_coupling_mismatch_is_absolute_difference (p q : ℚ) :
    maximalCouplingMismatchQ p q = |p - q| := by
  by_cases h : p ≤ q
  · have hdiff : p - q ≤ 0 := sub_nonpos.mpr h
    simp [maximalCouplingMismatchQ, maximalBernoulliCouplingQ,
      h, zero, one, abs_of_nonpos hdiff]
  · have hqp : q < p := lt_of_not_ge h
    have hdiff : 0 ≤ p - q := sub_nonneg.mpr (le_of_lt hqp)
    simp [maximalCouplingMismatchQ, maximalBernoulliCouplingQ,
      h, zero, one, abs_of_nonneg hdiff]

theorem bernoulli_total_variation_is_absolute_difference (p q : ℚ) :
    bernoulliTotalVariationQ p q = |p - q| := by
  by_cases h : p ≤ q
  · have hpq : p - q ≤ 0 := sub_nonpos.mpr h
    have hqp : 0 ≤ q - p := sub_nonneg.mpr h
    have hsecond : (1 - p) - (1 - q) = q - p := by ring
    simp [bernoulliTotalVariationQ, abs_of_nonpos hpq,
      abs_of_nonneg hqp, hsecond]
  · have hqp' : q < p := lt_of_not_ge h
    have hpq : 0 ≤ p - q := sub_nonneg.mpr (le_of_lt hqp')
    have hsecond : (1 - p) - (1 - q) = q - p := by ring
    have hsecond' : q - p ≤ 0 := sub_nonpos.mpr (le_of_lt hqp')
    simp [bernoulliTotalVariationQ, abs_of_nonneg hpq,
      abs_of_nonpos hsecond', hsecond]

theorem maximal_coupling_mismatch_equals_total_variation (p q : ℚ) :
    maximalCouplingMismatchQ p q = bernoulliTotalVariationQ p q := by
  calc
    maximalCouplingMismatchQ p q = |p - q| :=
      maximal_coupling_mismatch_is_absolute_difference p q
    _ = bernoulliTotalVariationQ p q :=
      (bernoulli_total_variation_is_absolute_difference p q).symm

end Book.Chapters.Chapter62
