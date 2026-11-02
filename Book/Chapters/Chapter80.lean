module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 80 — Certified Computation for Matrix-Geometric Tails

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter80

open Book.Models.FiniteTwoState

def dyadicTailBound (n : Nat) : Nat := 2 ^ n

theorem certifiedTailAtThree : dyadicTailBound 3 = 8 := by decide

end Book.Chapters.Chapter80
