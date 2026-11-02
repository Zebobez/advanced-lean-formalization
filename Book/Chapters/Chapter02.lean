module

public import Book.Chapters.Chapter01
public import Mathlib

public section

/-!
# Chapter 2 — Make Simplification Predictable

Extracted from manuscript/chapters/part-01/chapter-02-simp-normal-forms.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 4
example {α : Type _} (xs acc : List α) :
    Chapter01.reverseAcc xs acc = xs.reverse ++ acc := by
  simp

-- Source Lean fence 6
namespace Chapter02

def swapPair {α β : Type _} (p : α × β) : β × α :=
  (p.2, p.1)

-- Theorem 2.1: swapping twice is the identity.
@[simp] theorem swapPair_involutive {α β : Type _} (p : α × β) :
    swapPair (swapPair p) = p := by
  cases p
  rfl

example {α β : Type _} (p : α × β) :
    swapPair (swapPair (swapPair (swapPair p))) = p := by
  simp

end Chapter02

-- Source Lean fence 7
example {α : Type _} (xs : List α) : xs.reverse.reverse = xs := by
  simp

-- Source Lean fence 8
def addZeros (n : Nat) : Nat := (n + 0) + 0

theorem addZeros_eq (n : Nat) : addZeros n = n := by
  simp [addZeros]

-- Source Lean fence 10
example (n : Nat) : (n + 0) + 0 = n := by
  simp only [Nat.add_zero]

-- Source Lean fence 11
example (n m : Nat) (h : n = m) : n + 0 = m := by
  simpa using h

-- Source Lean fence 12
example (n m : Nat) (h : n + 0 = m) : n = m := by
  simpa using h

-- Source Lean fence 13
example (n m : Nat) (h : n + 0 = m) : n = m := by
  simp only [Nat.add_zero] at h
  exact h

-- Source Lean fence 14
namespace Chapter02

def chooseFrom {α : Type _} (p : Prop) [Decidable p] (yes no : α) : α :=
  if p then yes else no

@[simp] theorem chooseFrom_of_true {α : Type _} (p : Prop) [Decidable p]
    (hp : p) (yes no : α) : chooseFrom p yes no = yes := by
  simp [chooseFrom, hp]

@[simp] theorem chooseFrom_of_false {α : Type _} (p : Prop) [Decidable p]
    (hp : ¬ p) (yes no : α) : chooseFrom p yes no = no := by
  simp [chooseFrom, hp]

example {α : Type _} (p : Prop) [Decidable p] (hp : p) (yes no : α) :
    chooseFrom p yes no = yes := by
  exact chooseFrom_of_true p hp yes no

end Chapter02

-- Source Lean fence 15
example (a b c : ℤ) : a + b + c = c + b + a := by
  ring

