module

public import Mathlib

public section

/-!
# Chapter 25 — Linear Maps and Submodules

Extracted from manuscript/chapters/part-04/chapter-25-linear-maps-and-submodules.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter25

-- Source Lean fence 1
example {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (x y : M) :
    f (x + y) = f x + f y := by
  simp

-- Source Lean fence 2
example {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (x : M) :
    x ∈ LinearMap.ker f ↔ f x = 0 := by
  simp

end Book.Chapters.Chapter25
