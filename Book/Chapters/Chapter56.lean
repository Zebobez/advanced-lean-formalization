module

public import Mathlib

public section

/-!
# Chapter 56 — Uniformization and Poissonization

Extracted from manuscript/chapters/part-11/chapter-56-uniformization-and-poissonization.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter56

-- Source Lean fence 2
def IsStochastic {S : Type*} [Fintype S] (P : Matrix S S ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧
  (∀ x, ∑ y, P x y = 1)

structure Generator (S : Type*) [Fintype S] where
  rate : Matrix S S ℝ
  offDiag_nonneg : ∀ x y, x ≠ y → 0 ≤ rate x y
  row_sum_zero : ∀ x, ∑ y, rate x y = 0

end Book.Chapters.Chapter56
