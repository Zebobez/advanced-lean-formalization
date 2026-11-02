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
example {R : Type*} [CommRing R] (I : Ideal R) (x y : R) :
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

end Book.Chapters.Chapter30
