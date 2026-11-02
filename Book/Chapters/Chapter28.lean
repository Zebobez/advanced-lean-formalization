module

public import Mathlib

public section

/-!
# Chapter 28 — Group Actions, Orbits, and Stabilizers

Extracted from manuscript/chapters/part-04/chapter-28-group-actions-and-orbits.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter28

-- Source Lean fence 1
example {G X : Type*} [Group G] [MulAction G X]
    (a x : X) :
    x ∈ MulAction.orbit G a ↔ ∃ g : G, g • a = x := by
  exact MulAction.mem_orbit_iff

-- Source Lean fence 2
example {G X : Type*} [Group G] [MulAction G X]
    (a : X) : a ∈ MulAction.orbit G a := by
  rw [MulAction.mem_orbit_iff]
  exact ⟨1, one_smul G a⟩

-- Source Lean fence 4
example {G X : Type*} [Group G] [MulAction G X] (a : X)
    [Fintype G]
    [Fintype ↥(MulAction.orbit G a)]
    [Fintype ↥(MulAction.stabilizer G a)] :
    Fintype.card ↥(MulAction.orbit G a) *
      Fintype.card ↥(MulAction.stabilizer G a) = Fintype.card G := by
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G a

end Book.Chapters.Chapter28
