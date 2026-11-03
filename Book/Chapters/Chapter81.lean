module

public import Mathlib

public section

/-!
# Chapter 81 — Markovian Arrival Processes and MAP/M/1 Queues

Extracted from manuscript/chapters/part-22/chapter-81-markovian-arrivals-map-m1.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter81

-- Source Lean fence 1
abbrev MAPMatrix := Matrix (Fin 2) (Fin 2) ℚ

def mmppD0 : MAPMatrix := !![-3 / 2, 1; 2, -4]
def mmppD1 : MAPMatrix := !![1 / 2, 0; 0, 2]
def mmppPhaseGenerator : MAPMatrix := !![-1, 1; 2, -2]

def mmppStationary (i : Fin 2) : ℚ := if i = 0 then 2 / 3 else 1 / 3

def rowMultiply (p : Fin 2 → ℚ) (A : MAPMatrix) (j : Fin 2) : ℚ :=
  ∑ i : Fin 2, p i * A i j

def mapArrivalRate : ℚ :=
  ∑ i : Fin 2, mmppStationary i * (∑ j : Fin 2, mmppD1 i j)

def mmppAup : MAPMatrix := mmppD1
def mmppAwithin : MAPMatrix := !![-3, 1; 2, -11 / 2]
def mmppAdown : MAPMatrix := !![3 / 2, 0; 0, 3 / 2]
def mmppB00 : MAPMatrix := mmppD0
def mmppB01 : MAPMatrix := mmppD1
def mmppB10 : MAPMatrix := mmppAdown

theorem mmpp_phase_decomposition : mmppD0 + mmppD1 = mmppPhaseGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mmppD0, mmppD1, mmppPhaseGenerator,
    Matrix.add_apply]

theorem mmpp_stationary_normalized : ∑ i : Fin 2, mmppStationary i = 1 := by
  norm_num [mmppStationary]

theorem mmpp_stationary_phase_law :
    ∀ j : Fin 2, rowMultiply mmppStationary mmppPhaseGenerator j = 0 := by
  intro j
  fin_cases j <;>
    norm_num [rowMultiply, mmppStationary, mmppPhaseGenerator]

theorem mmpp_mean_arrival_rate_one : mapArrivalRate = 1 := by
  norm_num [mapArrivalRate, mmppStationary, mmppD1]

theorem mmppD1_nonnegative : ∀ i j : Fin 2, 0 ≤ mmppD1 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [mmppD1]

theorem mmppD0_offDiagonal_nonnegative :
    ∀ i j : Fin 2, i ≠ j → 0 ≤ mmppD0 i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [mmppD0] at *

theorem mmppAdown_nonnegative : ∀ i j : Fin 2, 0 ≤ mmppAdown i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [mmppAdown]

theorem mmpp_background_row_sum_zero (i : Fin 2) :
    ∑ j : Fin 2, (mmppD0 + mmppD1) i j = 0 := by
  fin_cases i <;> norm_num [mmppD0, mmppD1, Matrix.add_apply]

theorem mmpp_boundary_row_sum_zero (i : Fin 2) :
    ∑ j : Fin 2, (mmppB00 + mmppB01) i j = 0 := by
  simpa [mmppB00, mmppB01] using mmpp_background_row_sum_zero i

theorem mmpp_interior_row_sum_zero (i : Fin 2) :
    ∑ j : Fin 2, (mmppAdown + mmppAwithin + mmppAup) i j = 0 := by
  fin_cases i <;>
    norm_num [mmppAdown, mmppAwithin, mmppAup, mmppD1, Matrix.add_apply]

theorem mmpp_offered_load_is_stable : (mapArrivalRate / (3 / 2 : ℚ)) < 1 := by
  norm_num [mmpp_mean_arrival_rate_one]

end Book.Chapters.Chapter81
