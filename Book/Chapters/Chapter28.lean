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

-- Source Lean fence 5
theorem exercise_28_3_subgroup_fixes_iff_le_stabilizer
    {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (a : X) :
    (∀ g ∈ H, g • a = a) ↔ H ≤ MulAction.stabilizer G a := by
  constructor
  · intro h g hg
    rw [MulAction.mem_stabilizer_iff]
    exact h g hg
  · intro h g hg
    exact MulAction.mem_stabilizer_iff.mp (h hg)

-- Source Lean fence 6
theorem exercise_28_6_regular_orbit_one (G : Type*) [Group G] :
    MulAction.orbit G (1 : G) = Set.univ := by
  ext x
  rw [MulAction.mem_orbit_iff]
  simp

theorem exercise_28_6_regular_stabilizer_one (G : Type*) [Group G] :
    MulAction.stabilizer G (1 : G) = ⊥ := by
  ext g
  simp

end Book.Chapters.Chapter28
