module

public import Mathlib

public section

/-!
# Chapter 10 — Structured Rewriting with `calc` and `conv`

Extracted from manuscript/chapters/part-02/chapter-10-calculations-and-conv.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 1
namespace Chapter10

example {a b c : Nat} (h₁ : a = b) (h₂ : b ≤ c) : a ≤ c := by
  calc
    a = b := h₁
    _ ≤ c := h₂

-- Source Lean fence 2
example {a b c d : Nat}
    (hab : a = b) (hbc : b ≤ c) (hcd : c < d) : a < d := by
  calc
    a = b := hab
    _ ≤ c := hbc
    _ < d := hcd

-- Source Lean fence 3
example {a b c : Nat} (hab : a = b) (hbc : b ≤ c) :
    a + 1 ≤ c + 1 := by
  calc
    a + 1 = b + 1 := by rw [hab]
    _ ≤ c + 1 := Nat.add_le_add_right hbc 1

-- Source Lean fence 5
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  calc
    a + c = b + c := by rw [h]

-- Source Lean fence 6
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    arg 2
    rw [Nat.mul_comm]

-- Source Lean fence 7
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]

-- Source Lean fence 8
example (h : a + 0 = b) : a = b := by
  conv at h =>
    lhs
    rw [Nat.add_zero]
  exact h

-- Source Lean fence 9
example (a b : Nat) : a * b + b * a = 2 * (a * b) := by
  conv =>
    lhs
    arg 2
    rw [Nat.mul_comm]
  ring

