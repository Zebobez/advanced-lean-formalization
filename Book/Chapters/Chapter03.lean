module

public import Mathlib

public section

/-!
# Chapter 3 — State the Algebra You Need

Extracted from manuscript/chapters/part-01/chapter-03-algebraic-abstractions.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 1
universe u

namespace Chapter03

variable {M : Type u} [Monoid M]

theorem power_add_induction (a : M) (m n : Nat) :
    a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        a ^ (m + (n + 1)) = a ^ (m + n) * a := by
          rw [Nat.add_succ, pow_succ]
        _ = (a ^ m * a ^ n) * a := by
          rw [ih]
        _ = a ^ m * (a ^ n * a) := by
          rw [mul_assoc]
        _ = a ^ m * a ^ (n + 1) := by
          rw [pow_succ]

end Chapter03

-- Source Lean fence 5
example (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  exact Chapter03.power_add_induction a m n

-- Source Lean fence 6
#synth Monoid Nat

-- Source Lean fence 7
#check @Chapter03.power_add_induction

