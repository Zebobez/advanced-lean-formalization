module

public import Mathlib

public section

/-!
# Chapter 26 — Bases and Finite-Dimensional Arguments

Extracted from manuscript/chapters/part-04/chapter-26-bases-and-dimension.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter26

-- Source Lean fence 3
open Module

example {K V W : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W]
    {ι : Type*} (b : Basis ι K V)
    (f g : V →ₗ[K] W)
    (h : ∀ i, f (b i) = g (b i)) :
    f = g := by
  exact b.ext h

-- Source Lean fence 5
theorem exercise_26_2_basis_vector_coordinates
    {R M ι : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    (b : Basis ι R M) (i : ι) (a : R) :
    b.repr (a • b i) = Finsupp.single i a := by
  simp

-- Source Lean fence 6
theorem exercise_26_2_eq_of_basis_coordinates
    {R M ι : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    (b : Basis ι R M) {x y : M}
    (h : ∀ i, b.repr x i = b.repr y i) : x = y := by
  apply b.repr.injective
  ext i
  exact h i

-- Source Lean fence 7
theorem exercise_26_4_finrank_eq_card_of_basis
    {K V ι : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Fintype ι]
    (b : Basis ι K V) :
    Module.finrank K V = Fintype.card ι := by
  exact Module.finrank_eq_card_basis b

end Book.Chapters.Chapter26
