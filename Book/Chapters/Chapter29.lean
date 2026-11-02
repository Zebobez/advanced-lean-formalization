module

public import Mathlib

public section

/-!
# Chapter 29 — Polynomial Rings and Evaluation

Extracted from manuscript/chapters/part-04/chapter-29-polynomials-and-evaluation.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter29

-- Source Lean fence 1
example {R : Type*} [Semiring R] (a : R) :
    Polynomial.C a * Polynomial.X = Polynomial.monomial 1 a := by
  exact Polynomial.C_mul_X_eq_monomial

-- Source Lean fence 2
example {R : Type*} [CommRing R] (a : R) :
    (Polynomial.X - Polynomial.C a : Polynomial R).IsRoot a := by
  simp

-- Source Lean fence 4
example :
    Polynomial.aeval Complex.I
      (Polynomial.X ^ 2 + 1 : Polynomial ℝ) = 0 := by
  simp

-- Source Lean fence 5
theorem exercise_29_3_root_mul {R : Type*} [CommRing R]
    (p q : Polynomial R) (a : R)
    (hp : p.IsRoot a) : (p * q).IsRoot a := by
  rw [Polynomial.IsRoot.def] at hp ⊢
  simp [hp]

-- Source Lean fence 6
theorem exercise_29_1_eval_constant
    {R : Type*} [Semiring R] (a x : R) :
    (Polynomial.C a : Polynomial R).eval x = a := by
  simp

-- Source Lean fence 7
theorem exercise_29_4_eval₂_at_mapped_point
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (p : Polynomial R) (a : R) :
    p.eval₂ f (f a) = f (p.eval a) := by
  exact Polynomial.eval₂_at_apply f a

-- Source Lean fence 8
theorem exercise_29_7_factor_iff_root
    {R : Type*} [CommRing R] (p : Polynomial R) (a : R) :
    (Polynomial.X - Polynomial.C a) ∣ p ↔ p.IsRoot a := by
  exact Polynomial.dvd_iff_isRoot

end Book.Chapters.Chapter29
