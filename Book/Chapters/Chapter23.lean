module

public import Mathlib

public section

/-!
# Chapter 23 — Order Theory and Galois Connections

Extracted from manuscript/chapters/part-04/chapter-23-order-theory-and-galois-connections.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter23

-- Source Lean fence 1
example : Monotone (fun n : Nat => n + 1) := by
  intro a b hab
  exact Nat.add_le_add_right hab 1

-- Source Lean fence 2
def succOrderHom : Nat →o Nat where
  toFun n := n + 1
  monotone' := by
    intro a b hab
    exact Nat.add_le_add_right hab 1

-- Source Lean fence 3
theorem imagePreimageGC {α β : Type*} (f : α → β) :
    GaloisConnection
      (fun s : Set α => f '' s)
      (fun t : Set β => f ⁻¹' t) := by
  intro s t
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h hx

-- Source Lean fence 4
example {α β : Type*} [Preorder α] [Preorder β]
    {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) (a : α) (b : β) :
    l a ≤ b ↔ a ≤ u b := by
  exact gc a b

-- Source Lean fence 8
example {α β : Type*} [Preorder α] [Preorder β]
    {l : α → β} {u : β → α} (gc : GaloisConnection l u)
    {a : α} {b : β} (h₁ : l a ≤ b) : a ≤ u b := by
  have h₂ : a ≤ u b := (gc a b).mp h₁
  exact h₂

-- Source Lean fence 9
def doubleOrderHom : Nat →o Nat where
  toFun n := 2 * n
  monotone' := by
    intro a b hab
    exact Nat.mul_le_mul_left 2 hab

theorem exercise_23_1_unbundled {a b : Nat} (hab : a ≤ b) :
    2 * a ≤ 2 * b := by
  exact doubleOrderHom.monotone hab

-- Source Lean fence 10
theorem exercise_23_2_image_subset_preimage
    {α β : Type*} (f : α → β) (s : Set α) (t : Set β)
    (h : f '' s ⊆ t) : s ⊆ f ⁻¹' t := by
  exact (imagePreimageGC f s t).mp h

-- Source Lean fence 11
theorem exercise_23_3_unit
    {α β : Type*} (f : α → β) (s : Set α) :
    s ⊆ f ⁻¹' (f '' s) := by
  exact (imagePreimageGC f s (f '' s)).mp Set.Subset.rfl

theorem exercise_23_3_counit
    {α β : Type*} (f : α → β) (t : Set β) :
    f '' (f ⁻¹' t) ⊆ t := by
  exact (imagePreimageGC f (f ⁻¹' t) t).mpr Set.Subset.rfl

-- Source Lean fence 12
theorem exercise_23_5_left_adjoint_preserves_sup
    {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    {l : α → β} {u : β → α} (gc : GaloisConnection l u)
    (a b : α) : l (a ⊔ b) = l a ⊔ l b := by
  apply le_antisymm
  · apply gc.l_le
    apply sup_le
    · exact (gc a (l a ⊔ l b)).mp le_sup_left
    · exact (gc b (l a ⊔ l b)).mp le_sup_right
  · exact sup_le (gc.monotone_l le_sup_left) (gc.monotone_l le_sup_right)

-- Source Lean fence 13
example (s t : Set Nat) :
    (fun _ : Nat => ()) '' (s ∪ t) =
      ((fun _ : Nat => ()) '' s ∪ (fun _ : Nat => ()) '' t) := by
  exact Set.image_union _ _ _

example :
    (fun _ : Nat => ()) '' ({0} ∩ {1} : Set Nat) ≠
      ((fun _ : Nat => ()) '' ({0} : Set Nat) ∩
       (fun _ : Nat => ()) '' ({1} : Set Nat)) := by
  intro h
  have hmem : () ∈
      ((fun _ : Nat => ()) '' ({0} : Set Nat) ∩
       (fun _ : Nat => ()) '' ({1} : Set Nat)) := by
    simp
  rw [← h] at hmem
  simp at hmem

end Book.Chapters.Chapter23
