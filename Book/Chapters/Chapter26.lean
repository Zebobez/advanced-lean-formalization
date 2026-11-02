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

end Book.Chapters.Chapter26
