module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 36 — Filtrations and Martingales

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter36

open Book.Models.FiniteTwoState

def martingaleDifference : State → Int := fun s => if s = zero then -1 else 1

theorem fairDifferenceHasZeroMean :
    expectationNumerator uniformWeight martingaleDifference = 0 := by decide

end Book.Chapters.Chapter36
