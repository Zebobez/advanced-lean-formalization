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
example {R : Type*} [CommRing R] (p q : Polynomial R) (a : R)
    (hp : p.IsRoot a) : (p * q).IsRoot a := by
  rw [Polynomial.IsRoot.def] at hp ⊢
  simp [hp]

end Book.Chapters.Chapter29
