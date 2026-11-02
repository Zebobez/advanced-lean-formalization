module

public import Mathlib

public section

/-!
# Chapter 30 — Ideals and Quotient Rings

Extracted from manuscript/chapters/part-04/chapter-30-ideals-and-quotient-rings.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter30

-- Source Lean fence 1
example {R : Type*} [CommRing R] (I J : Ideal R) (x : R) :
    x ∈ I ⊔ J ↔ ∃ y ∈ I, ∃ z ∈ J, y + z = x := by
  simp [Submodule.mem_sup]

-- Source Lean fence 2
example {R : Type*} [CommRing R] (I : Ideal R) :
    R →+* R ⧸ I :=
  Ideal.Quotient.mk I

-- Source Lean fence 3
theorem exercise_30_2_quotient_eq_iff_sub_mem
    {R : Type*} [CommRing R] (I : Ideal R) (x y : R) :
    Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ x - y ∈ I := by
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem x y

-- Source Lean fence 4
example {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S)
    (h : I ≤ RingHom.ker f) : R ⧸ I →+* S :=
  Ideal.Quotient.lift I f h

-- Source Lean fence 5
noncomputable example {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : R ⧸ RingHom.ker f ≃+* f.range :=
  RingHom.quotientKerEquivRange f

-- Source Lean fence 6
theorem exercise_30_1_quotient_map_kernel
    {R : Type*} [CommRing R] (I : Ideal R) :
    RingHom.ker (Ideal.Quotient.mk I) = I := by
  simp

-- Source Lean fence 7
theorem exercise_30_3_lift_mk
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S)
    (h : ∀ a : R, a ∈ I → f a = 0) (r : R) :
    Ideal.Quotient.lift I f h (Ideal.Quotient.mk I r) = f r := by
  exact Ideal.Quotient.lift_mk I f h

-- Source Lean fence 8
theorem exercise_30_5_maximal_iff_field_quotient
    {R : Type*} [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ IsField (R ⧸ I) := by
  exact Ideal.Quotient.maximal_ideal_iff_isField_quotient I

-- Source Lean fence 9
theorem exercise_30_6_map_le_iff_comap
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) :
    Ideal.map f I ≤ J ↔ I ≤ Ideal.comap f J := by
  exact Ideal.map_le_iff_le_comap

end Book.Chapters.Chapter30
