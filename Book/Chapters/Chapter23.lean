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
example {α β : Type*} (f : α → β) :
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

end Book.Chapters.Chapter23
