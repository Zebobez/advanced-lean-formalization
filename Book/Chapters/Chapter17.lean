module

public import Mathlib

public section

/-!
# Chapter 17 — Composing Automation Safely

Extracted from manuscript/chapters/part-02/chapter-17-composing-automation.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter17

-- Source Lean fence 2
example (p q : Prop) (hp : p) : p ∧ p := by
  constructor <;> assumption

-- Source Lean fence 3
example (n : Nat) : n = n := by
  first
  | assumption
  | rfl

-- Source Lean fence 4
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

-- Source Lean fence 5
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- Source Lean fence 6
example (p q r : Prop) : p → q → r → p := by
  intro hp
  intro hq
  intro hr
  exact hp

-- Source Lean fence 7
example (p q r : Prop)
    (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  solve_by_elim

-- Source Lean fence 8
example (p q r s : Prop)
    (hp : p) (hpq : p → q) (hqr : q → r) (hrs : r → s) : s := by
  have hr : r := by
    solve_by_elim [hpq, hqr]
  exact hrs hr

-- Source Lean fence 9
example (p q : Prop) (hp : p) : p ∨ q := by
  aesop

-- Source Lean fence 10
example (p q : Prop) (hp : p) : p ∨ q := by
  exact Or.inl hp

end Book.Chapters.Chapter17
