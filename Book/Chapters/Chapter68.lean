module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 68 — The Markov Chain Tree Theorem

Extracted from manuscript/chapters/part-16/chapter-68-markov-chain-tree-theorem.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter68

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def treeWeightAtZero : Nat := 2
def treeWeightAtOne : Nat := 1

theorem incomingTreeWeightsBalance :
    treeWeightAtZero * 1 = treeWeightAtOne * 2 := by decide

-- Source Lean fence 3
inductive CycleState where
  | zero
  | one
  | two
  deriving DecidableEq

def cycleTreeWeight (a b c : Nat) : CycleState → Nat
  | .zero => b * c
  | .one => c * a
  | .two => a * b

theorem cycleTreeWeights_balance (a b c : Nat) :
    cycleTreeWeight a b c .zero * a =
        cycleTreeWeight a b c .one * b ∧
      cycleTreeWeight a b c .one * b =
        cycleTreeWeight a b c .two * c := by
  constructor <;> simp [cycleTreeWeight] <;> ring

theorem cycleTreeWeights_all_equal_flow (a b c : Nat) :
    cycleTreeWeight a b c .zero * a =
        cycleTreeWeight a b c .one * b ∧
      cycleTreeWeight a b c .one * b =
        cycleTreeWeight a b c .two * c ∧
      cycleTreeWeight a b c .two * c =
        cycleTreeWeight a b c .zero * a := by
  obtain ⟨h₀₁, h₁₂⟩ := cycleTreeWeights_balance a b c
  refine ⟨h₀₁, h₁₂, ?_⟩
  simp [cycleTreeWeight]
  ring

theorem cycleTreeWeight_positive (a b c : Nat)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < cycleTreeWeight a b c .zero ∧
      0 < cycleTreeWeight a b c .one ∧
      0 < cycleTreeWeight a b c .two := by
  simp [cycleTreeWeight, ha, hb, hc]

end Book.Chapters.Chapter68
