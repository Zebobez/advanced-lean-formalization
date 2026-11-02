module

public import Mathlib

public section

/-!
# Chapter 22 — Classical Reasoning and Computability

Extracted from manuscript/chapters/part-03/chapter-22-classical-reasoning-and-computability.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter22

-- Source Lean fence 1
theorem doubleNegation (p : Prop) : ¬¬p → p := by
  classical
  intro h
  by_contra hp
  exact h hp

-- Source Lean fence 2
theorem has_witness {α : Type} {P : α → Prop} (h : ∃ x, P x) :
    ∃ x, P x := h

-- Source Lean fence 3
universe u

noncomputable def selectWitness {α : Type u} {P : α → Prop}
    (h : ∃ x, P x) : α :=
  Classical.choose h

theorem selectWitness_spec {α : Type u} {P : α → Prop}
    (h : ∃ x, P x) : P (selectWitness h) :=
  Classical.choose_spec h

-- Source Lean fence 4
noncomputable def arbitraryElement (α : Type) [Nonempty α] : α :=
  Classical.choice ‹Nonempty α›

end Book.Chapters.Chapter22
