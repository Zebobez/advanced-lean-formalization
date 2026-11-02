module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 84 — GI/M/1-Type Chains and Geometric Stationary Tails

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter84

open Book.Models.FiniteTwoState

def geometricTail (n : Nat) : Nat := 2 ^ n

theorem firstThreeLevelsHaveTailWeightEight : geometricTail 3 = 8 := by decide

end Book.Chapters.Chapter84
