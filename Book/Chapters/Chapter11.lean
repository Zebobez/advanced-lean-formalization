module

public import Mathlib

public section

/-!
# Chapter 11 — Arithmetic and Decision Procedures

Extracted from manuscript/chapters/part-02/chapter-11-arithmetic.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter11

-- Source Lean fence 1
example : (37 : Nat) % 5 = 2 := by
  norm_num

example : (3 : Int) ^ 4 - 5 = 76 := by
  norm_num

-- Source Lean fence 2
example (n m : Nat) (h₁ : n ≤ m) (h₂ : m < n + 4) : m - n < 4 := by
  omega

-- Source Lean fence 3
example (a b : Nat) (h : a ≤ b) : a + (b - a) = b := by
  omega

-- Source Lean fence 4
example (x y : Int) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

-- Source Lean fence 5
example (a b c : Int) (h : c = b * a + a * b) : c = 2 * a * b := by
  rw [h]
  ring

-- Source Lean fence 6
example {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  positivity

-- Source Lean fence 7
example {a b : Nat} (h : a ≤ b) : a + 1 ≤ b + 1 := by
  exact Nat.add_le_add_right h 1

end Book.Chapters.Chapter11
