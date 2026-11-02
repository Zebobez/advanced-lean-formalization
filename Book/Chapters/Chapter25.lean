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

-- Source Lean fence 4
theorem exercise_25_2_kernel_is_comap
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) :
    LinearMap.ker f = Submodule.comap f ⊥ := by
  rfl

theorem exercise_25_2_kernel_membership
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (x : M) :
    x ∈ LinearMap.ker f ↔ f x = 0 := by
  change f x ∈ (⊥ : Submodule R N) ↔ f x = 0
  simp

-- Source Lean fence 5
theorem exercise_25_3_map_le_iff_comap
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (E : Submodule R M) (F : Submodule R N) :
    Submodule.map f E ≤ F ↔ E ≤ Submodule.comap f F := by
  simpa using
    (Submodule.map_le_iff_le_comap
      (f := (f : M →ₛₗ[RingHom.id R] N)) (p := E) (q := F))

-- Source Lean fence 6
theorem exercise_25_4_injective_iff_kernel_eq_bot
    {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Injective f ↔ LinearMap.ker f = ⊥ := by
  simpa using
    (LinearMap.ker_eq_bot
      (f := (f : M →ₛₗ[RingHom.id R] N))).symm

end Book.Chapters.Chapter25
