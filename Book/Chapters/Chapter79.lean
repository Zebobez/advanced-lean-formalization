module

public import Mathlib

public section

/-!
# Chapter 79 — Quasi-Birth–Death Processes and Matrix-Analytic Methods

Extracted from manuscript/chapters/part-22/chapter-79-quasi-birth-death-processes.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter79

-- Source Lean fence 1
abbrev QBDMatrix := Matrix (Fin 2) (Fin 2) ℚ

def qbdInteriorPolynomial (Aup Amid Adown R : QBDMatrix) : QBDMatrix :=
  Aup + R * Amid + R ^ 2 * Adown

def qbdInteriorResidual (Aup Amid Adown R : QBDMatrix) (k : Nat) : QBDMatrix :=
  R ^ k * Aup + R ^ (k + 1) * Amid + R ^ (k + 2) * Adown

theorem qbdInteriorResidual_factorization
    (Aup Amid Adown R : QBDMatrix) (k : Nat) :
    qbdInteriorResidual Aup Amid Adown R k =
      R ^ k * qbdInteriorPolynomial Aup Amid Adown R := by
  unfold qbdInteriorResidual qbdInteriorPolynomial
  have h1 : R ^ (k + 1) = R ^ k * R := by rw [pow_succ]
  have h2 : R ^ (k + 2) = R ^ k * R ^ 2 := by rw [pow_add]
  rw [h1, h2]
  noncomm_ring

def qbdUp : QBDMatrix := !![0, 1; 0, 0]
def qbdWithin : QBDMatrix := !![-2, 0; 0, -2]
def qbdDown : QBDMatrix := !![1, 0; 0, 2]
def qbdRate : QBDMatrix := !![0, (1 : ℚ) / 2; 0, 0]

theorem qbdRate_solves_polynomial :
    qbdInteriorPolynomial qbdUp qbdWithin qbdDown qbdRate = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qbdInteriorPolynomial, qbdUp, qbdWithin, qbdDown, qbdRate,
      pow_two, Matrix.mul_apply]

theorem qbdRate_square_zero : qbdRate ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qbdRate, pow_two, Matrix.mul_apply]

theorem qbdInteriorResidual_zero (k : Nat) :
    qbdInteriorResidual qbdUp qbdWithin qbdDown qbdRate k = 0 := by
  rw [qbdInteriorResidual_factorization, qbdRate_solves_polynomial]
  simp

theorem qbdUp_nonnegative : ∀ i j, 0 ≤ qbdUp i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [qbdUp]

theorem qbdDown_nonnegative : ∀ i j, 0 ≤ qbdDown i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [qbdDown]

theorem qbdRate_nonnegative : ∀ i j, 0 ≤ qbdRate i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [qbdRate]

theorem qbdWithin_offDiagonal_nonnegative :
    ∀ i j, i ≠ j → 0 ≤ qbdWithin i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [qbdWithin] at *

theorem qbdInterior_row_sum_zero (i : Fin 2) :
    ∑ j : Fin 2, (qbdUp + qbdWithin + qbdDown) i j = 0 := by
  fin_cases i <;>
    norm_num [qbdUp, qbdWithin, qbdDown, Matrix.add_apply]

end Book.Chapters.Chapter79
