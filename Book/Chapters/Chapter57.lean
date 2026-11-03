module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 57 — Sample Paths and Non-Explosion

Extracted from manuscript/chapters/part-11/chapter-57-sample-paths-and-non-explosion.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter57

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def alternatingPath (time : Nat) : State := if time % 2 = 0 then zero else one

theorem pathStartsAtZero : alternatingPath 0 = zero := by decide
theorem pathMovesToOne : alternatingPath 1 = one := by decide

-- Source Lean fence 2
open scoped BigOperators

def finitePathJumpCount {α : Type*} [DecidableEq α] {N : Nat}
    (path : Fin (N + 1) → α) : Nat :=
  ∑ i : Fin N, if path i.castSucc = path i.succ then 0 else 1

theorem genuine_changes_le_candidate_events {α : Type*} [DecidableEq α]
    {N : Nat} (path : Fin (N + 1) → α) : finitePathJumpCount path ≤ N := by
  unfold finitePathJumpCount
  calc
    _ ≤ ∑ _i : Fin N, (1 : Nat) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs <;> omega
    _ = N := by simp

end Book.Chapters.Chapter57
