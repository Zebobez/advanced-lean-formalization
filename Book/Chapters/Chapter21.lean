module

public import Mathlib

public section

/-!
# Chapter 21 — Dependent Equality and Transport

Extracted from manuscript/chapters/part-03/chapter-21-dependent-equality-and-transport.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter21

-- Source Lean fence 1
example {α : Type} {a b : α}
    (h : a = b) (P : α → Prop) (ha : P a) : P b := by
  exact h ▸ ha

-- Source Lean fence 3
def moveFin {n m : Nat} (h : n = m) (i : Fin n) : Fin m :=
  h ▸ i

-- Source Lean fence 4
example {α : Type} {a b : α}
    (h : a = b) (P : α → Prop) (ha : P a) : P b := by
  cases h
  exact ha

-- Source Lean fence 5
example (n m : Nat) (h : n = m) : n + 1 = m + 1 := by
  rw [h]

-- Source Lean fence 6
example (n m : Nat) (h : n = m) : n + 1 = m + 1 := by
  subst m
  rfl

-- Source Lean fence 8
def moveFinBack {n m : Nat} (h : n = m) (i : Fin m) : Fin n :=
  h.symm ▸ i

-- Source Lean fence 9
example {α β : Type} (f : α → β) {a b : α} (h : a = b) :
    f a = f b := by
  exact congrArg f h

-- Source Lean fence 10
example (a b c d : Nat) (h₁ : a = c) (h₂ : b = d) :
    a + b = c + d := by
  rw [h₁, h₂]

end Book.Chapters.Chapter21
