module

public import Mathlib

public section

/-!
# Chapter 88 — Newton Linearization for Matrix Rate Equations

Extracted from manuscript/chapters/part-22/chapter-88-newton-methods-for-matrix-rate-equations.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter88

-- Source Lean fence 1
def scalarResidual (x : ℚ) : ℚ := 1 / 10 - (4 / 5) * x + (7 / 10) * x ^ 2
def scalarResidualDerivative (x : ℚ) : ℚ := -(4 / 5) + (7 / 5) * x
def scalarNewtonStep (x : ℚ) : ℚ := x - scalarResidual x / scalarResidualDerivative x

theorem scalarResidual_factorization (x : ℚ) :
    scalarResidual x = ((7 * x - 1) * (x - 1)) / 10 := by
  unfold scalarResidual
  ring

theorem scalarNewton_first_step : scalarNewtonStep 0 = 1 / 8 := by
  norm_num [scalarNewtonStep, scalarResidual, scalarResidualDerivative]

theorem scalarNewton_second_step : scalarNewtonStep (1 / 8) = 57 / 400 := by
  norm_num [scalarNewtonStep, scalarResidual, scalarResidualDerivative]

theorem scalarNewton_bad_step : scalarNewtonStep (1 / 2) = -(3 / 4) := by
  norm_num [scalarNewtonStep, scalarResidual, scalarResidualDerivative]

abbrev NewtonMatrix := Matrix (Fin 2) (Fin 2) ℚ

def exampleX : NewtonMatrix := !![1, 1; 0, 1]
def exampleH : NewtonMatrix := !![0, 0; 1, 0]

theorem matrix_square_increment_expansion (X H : NewtonMatrix) :
    (X + H) ^ 2 = X ^ 2 + X * H + H * X + H ^ 2 := by
  simp only [pow_two, add_mul, mul_add]
  abel

theorem matrix_square_first_order_remainder (X H : NewtonMatrix) :
    (X + H) ^ 2 - X ^ 2 - (X * H + H * X) = H ^ 2 := by
  rw [matrix_square_increment_expansion]
  abel

theorem exampleXH_order_is_not_commutative :
    exampleX * exampleH ≠ exampleH * exampleX := by
  intro h
  have h11 := congrArg (fun M : NewtonMatrix => M 1 1) h
  norm_num [exampleX, exampleH, Matrix.mul_apply] at h11

theorem example_linearization_not_twice_left_product :
    exampleX * exampleH + exampleH * exampleX ≠ 2 • (exampleX * exampleH) := by
  intro h
  have h00 := congrArg (fun M : NewtonMatrix => M 0 0) h
  norm_num [exampleX, exampleH, Matrix.mul_apply] at h00

end Book.Chapters.Chapter88
