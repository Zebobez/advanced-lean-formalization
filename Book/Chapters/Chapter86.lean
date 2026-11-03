module

public import Mathlib

public section

/-!
# Chapter 86 — Spectral Asymptotics of Matrix-Geometric Tails

Extracted from manuscript/chapters/part-22/chapter-86-spectral-asymptotics-of-matrix-geometric-tails.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter86

-- Source Lean fence 1
abbrev SpectralMatrix := Matrix (Fin 2) (Fin 2) ℚ

def spectralR : SpectralMatrix := !![3 / 10, 1 / 10; 1 / 5, 2 / 5]
def spectralResolvent : SpectralMatrix := !![3 / 2, 1 / 4; 1 / 2, 7 / 4]

def spectralRight (i : Fin 2) : ℚ := if i = 0 then 1 else 2
def spectralLeft (_i : Fin 2) : ℚ := 1 / 3
def spectralSecondRight (i : Fin 2) : ℚ := if i = 0 then 1 else -1
def spectralBoundary (i : Fin 2) : ℚ := if i = 0 then 1 / 2 else 1 / 18
def spectralOnes (_i : Fin 2) : ℚ := 1

def spectralMatVec (A : SpectralMatrix) (v : Fin 2 → ℚ) (i : Fin 2) : ℚ :=
  ∑ j : Fin 2, A i j * v j

def spectralRowVec (u : Fin 2 → ℚ) (A : SpectralMatrix) (j : Fin 2) : ℚ :=
  ∑ i : Fin 2, u i * A i j

def spectralDot (u v : Fin 2 → ℚ) : ℚ :=
  ∑ i : Fin 2, u i * v i

def spectralProjection (i j : Fin 2) : ℚ := spectralRight i * spectralLeft j

def spectralCharacteristic (x : ℚ) : ℚ :=
  (3 / 10 - x) * (2 / 5 - x) - 1 / 50

theorem spectralR_positive : ∀ i j : Fin 2, 0 < spectralR i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [spectralR]

theorem spectral_right_eigenvector :
    ∀ i : Fin 2,
      spectralMatVec spectralR spectralRight i = (1 / 2 : ℚ) * spectralRight i := by
  intro i
  fin_cases i <;> norm_num [spectralMatVec, spectralR, spectralRight]

theorem spectral_left_eigenvector :
    ∀ j : Fin 2,
      spectralRowVec spectralLeft spectralR j = (1 / 2 : ℚ) * spectralLeft j := by
  intro j
  fin_cases j <;> norm_num [spectralRowVec, spectralLeft, spectralR]

theorem spectral_perron_pair_normalized :
    spectralDot spectralLeft spectralRight = 1 := by
  norm_num [spectralDot, spectralLeft, spectralRight]

theorem spectral_second_eigenvector :
    ∀ i : Fin 2,
      spectralMatVec spectralR spectralSecondRight i =
        (1 / 5 : ℚ) * spectralSecondRight i := by
  intro i
  fin_cases i <;> norm_num [spectralMatVec, spectralR, spectralSecondRight]

theorem spectral_characteristic_factorization (x : ℚ) :
    spectralCharacteristic x = (x - 1 / 2) * (x - 1 / 5) := by
  unfold spectralCharacteristic
  ring

theorem spectral_projection_idempotent (i j : Fin 2) :
    ∑ k : Fin 2, spectralProjection i k * spectralProjection k j =
      spectralProjection i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [spectralProjection, spectralRight, spectralLeft]

theorem spectralResolvent_left_inverse :
    (1 - spectralR) * spectralResolvent = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spectralR, spectralResolvent, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.one_apply]

theorem spectralResolvent_right_inverse :
    spectralResolvent * (1 - spectralR) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spectralR, spectralResolvent, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.one_apply]

theorem spectralResolvent_apply_ones :
    ∀ i : Fin 2, spectralMatVec spectralResolvent spectralOnes i =
      (if i = 0 then 7 / 4 else 9 / 4) := by
  intro i
  fin_cases i <;>
    norm_num [spectralMatVec, spectralResolvent, spectralOnes]

theorem spectralBoundary_normalized :
    spectralDot spectralBoundary
      (fun i => if i = 0 then 7 / 4 else 9 / 4) = 1 := by
  norm_num [spectralDot, spectralBoundary]

theorem spectralBoundary_dot_right :
    spectralDot spectralBoundary spectralRight = 11 / 18 := by
  norm_num [spectralDot, spectralBoundary, spectralRight]

theorem spectralLeft_mass : (∑ i : Fin 2, spectralLeft i) = 2 / 3 := by
  norm_num [spectralLeft]

theorem spectralTailConstant :
    (spectralDot spectralBoundary spectralRight) *
      (∑ i : Fin 2, spectralLeft i) / (1 - 1 / 2) = 22 / 27 := by
  norm_num [spectralDot, spectralBoundary, spectralRight, spectralLeft]

theorem spectralAsymptoticAmplitude (i : Fin 2) :
    spectralDot spectralBoundary spectralRight * spectralLeft i = 11 / 54 := by
  fin_cases i <;> norm_num [spectralDot, spectralBoundary, spectralRight, spectralLeft]

end Book.Chapters.Chapter86
