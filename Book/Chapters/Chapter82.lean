module

public import Book.Chapters.Chapter81
public import Mathlib

public section

/-!
# Chapter 82 — Phase-Type Service and MAP/PH/1 Queues

Extracted from manuscript/chapters/part-22/chapter-82-phase-type-service-map-ph1.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter82

-- Source Lean fence 1

open Book.Chapters.Chapter81

abbrev PHMatrix := Matrix (Fin 2) (Fin 2) ℚ

def erlangT : PHMatrix := !![-3, 3; 0, -3]
def erlangNegT : PHMatrix := !![3, -3; 0, 3]
def erlangBeta (i : Fin 2) : ℚ := if i = 0 then 1 else 0
def erlangExitRate (i : Fin 2) : ℚ := if i = 0 then 0 else 3
def erlangOnes (_i : Fin 2) : ℚ := 1
def erlangMeanSolve (i : Fin 2) : ℚ := if i = 0 then 2 / 3 else 1 / 3
def erlangSecondSolve (i : Fin 2) : ℚ := if i = 0 then 1 / 3 else 1 / 9

def matrixVector (A : PHMatrix) (x : Fin 2 → ℚ) (i : Fin 2) : ℚ :=
  ∑ j : Fin 2, A i j * x j

def rowVectorPairing (p x : Fin 2 → ℚ) : ℚ :=
  ∑ i : Fin 2, p i * x i

theorem erlangNegT_is_negative_T : erlangNegT = -erlangT := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [erlangNegT, erlangT]

theorem erlangBeta_probability : (∑ i : Fin 2, erlangBeta i) = 1 := by
  norm_num [erlangBeta]

theorem erlangT_offDiagonal_nonnegative :
    ∀ i j : Fin 2, i ≠ j → 0 ≤ erlangT i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [erlangT] at *

theorem erlang_exit_rate_matches_row_sum :
    ∀ i : Fin 2, erlangExitRate i = -∑ j : Fin 2, erlangT i j := by
  intro i
  fin_cases i <;> norm_num [erlangExitRate, erlangT, Matrix.add_apply]

theorem erlangMeanSolve_solves :
    ∀ i : Fin 2, matrixVector erlangNegT erlangMeanSolve i = erlangOnes i := by
  intro i
  fin_cases i <;>
    norm_num [matrixVector, erlangNegT, erlangMeanSolve, erlangOnes,
      Matrix.mul_apply]

theorem erlangSecondSolve_solves :
    ∀ i : Fin 2,
      matrixVector erlangNegT erlangSecondSolve i = erlangMeanSolve i := by
  intro i
  fin_cases i <;>
    norm_num [matrixVector, erlangNegT, erlangSecondSolve, erlangMeanSolve,
      Matrix.mul_apply]

theorem erlangMean_is_two_thirds :
    rowVectorPairing erlangBeta erlangMeanSolve = 2 / 3 := by
  norm_num [rowVectorPairing, erlangBeta, erlangMeanSolve]

theorem erlangSecondMoment_is_two_thirds :
    2 * rowVectorPairing erlangBeta erlangSecondSolve = 2 / 3 := by
  norm_num [rowVectorPairing, erlangBeta, erlangSecondSolve]

theorem erlangVariance_is_two_ninths :
    2 * rowVectorPairing erlangBeta erlangSecondSolve -
      (rowVectorPairing erlangBeta erlangMeanSolve) ^ 2 = 2 / 9 := by
  norm_num [rowVectorPairing, erlangBeta, erlangSecondSolve, erlangMeanSolve]

theorem mmppErlangTrafficLoad :
    mapArrivalRate * rowVectorPairing erlangBeta erlangMeanSolve = 2 / 3 := by
  rw [mmpp_mean_arrival_rate_one, erlangMean_is_two_thirds]
  norm_num

theorem mmppErlangTrafficLoad_lt_one :
    mapArrivalRate * rowVectorPairing erlangBeta erlangMeanSolve < 1 := by
  rw [mmppErlangTrafficLoad]
  norm_num

end Book.Chapters.Chapter82
