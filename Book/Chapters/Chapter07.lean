module

public import Mathlib

public section

/-!
# Chapter 7 — Functional Induction and Well-Founded Recursion

Extracted from manuscript/chapters/part-01/chapter-07-well-founded-recursion.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 1
namespace Chapter07

def halfSteps : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + halfSteps ((n + 1) / 2)
termination_by n => n
decreasing_by
  simp_wf
  omega

-- Source Lean fence 2
@[simp] theorem halfSteps_zero : halfSteps 0 = 0 := by
  simp [halfSteps]

@[simp] theorem halfSteps_succ (n : Nat) :
    halfSteps (n + 1) = 1 + halfSteps ((n + 1) / 2) := by
  simp [halfSteps]

-- Source Lean fence 4
theorem halfSteps_le (n : Nat) : halfSteps n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [halfSteps]
      | succ k =>
          rw [halfSteps_succ]
          have hsmall : (k + 1) / 2 < k + 1 := by omega
          have hbound := ih ((k + 1) / 2) hsmall
          omega

-- Source Lean fence 5
example (n : Nat) : halfSteps (n + 1) = 1 + halfSteps ((n + 1) / 2) := by
  rw [halfSteps_succ]

