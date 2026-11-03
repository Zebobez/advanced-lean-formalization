module

public import Mathlib

public section

/-!
# Chapter 89 — Certified Enclosures for Rate Matrices

Extracted from manuscript/chapters/part-22/chapter-89-certified-rate-matrix-enclosures.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter89

-- Source Lean fence 1
abbrev EnclosureMatrix := Matrix (Fin 2) (Fin 2) ℚ

def enclosureC0 : EnclosureMatrix := !![2 / 25, 1 / 100; 1 / 50, 7 / 100]
def enclosureC1 : EnclosureMatrix := !![1 / 5, 1 / 10; 0, 1 / 5]
def enclosureUpper : EnclosureMatrix := !![13 / 100, 1 / 20; 1 / 25, 3 / 25]
def enclosureCandidate : EnclosureMatrix := !![1 / 10, 1 / 40; 1 / 40, 9 / 100]
def enclosureRoot : EnclosureMatrix := !![1 / 10, 1 / 40; 1 / 40, 29 / 320]

def affineRateMap (X : EnclosureMatrix) : EnclosureMatrix := enclosureC0 + X * enclosureC1

def matrixInfinityNorm2 (A : EnclosureMatrix) : ℚ :=
  max (∑ j : Fin 2, |A 0 j|) (∑ j : Fin 2, |A 1 j|)

def enclosureResidual : EnclosureMatrix :=
  affineRateMap enclosureCandidate - enclosureCandidate

theorem enclosureC0_nonnegative : ∀ i j : Fin 2, 0 ≤ enclosureC0 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [enclosureC0]

theorem enclosureC1_nonnegative : ∀ i j : Fin 2, 0 ≤ enclosureC1 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [enclosureC1]

theorem enclosureC1_infinity_norm : matrixInfinityNorm2 enclosureC1 = 3 / 10 := by
  norm_num [matrixInfinityNorm2, enclosureC1]

theorem enclosure_upper_supersolution :
    ∀ i j : Fin 2, affineRateMap enclosureUpper i j ≤ enclosureUpper i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [affineRateMap, enclosureC0, enclosureC1, enclosureUpper,
      Matrix.add_apply, Matrix.mul_apply]

theorem enclosure_candidate_in_box :
    (∀ i j : Fin 2, 0 ≤ enclosureCandidate i j) ∧
      (∀ i j : Fin 2, enclosureCandidate i j ≤ enclosureUpper i j) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [enclosureCandidate, enclosureUpper]

theorem enclosure_root_is_fixed : affineRateMap enclosureRoot = enclosureRoot := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [affineRateMap, enclosureC0, enclosureC1, enclosureRoot,
      Matrix.add_apply, Matrix.mul_apply]

theorem enclosure_root_in_box :
    (∀ i j : Fin 2, 0 ≤ enclosureRoot i j) ∧
      (∀ i j : Fin 2, enclosureRoot i j ≤ enclosureUpper i j) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [enclosureRoot, enclosureUpper]

theorem enclosure_residual_exact :
    enclosureResidual = !![0, 0; 0, (1 : ℚ) / 2000] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [enclosureResidual, affineRateMap, enclosureC0, enclosureC1,
      enclosureCandidate, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]

theorem enclosure_residual_norm : matrixInfinityNorm2 enclosureResidual = 1 / 2000 := by
  rw [enclosure_residual_exact]
  norm_num [matrixInfinityNorm2]

theorem enclosure_contraction_factor_lt_one : (3 / 10 : ℚ) < 1 := by norm_num

theorem enclosure_residual_error_bound :
    (1 / 2000 : ℚ) / (1 - 3 / 10) = 1 / 1400 := by
  norm_num

end Book.Chapters.Chapter89
