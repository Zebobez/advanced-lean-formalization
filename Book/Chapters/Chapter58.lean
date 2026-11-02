module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 58 — Dynkin’s Formula and Generator Martingales

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter58

open Book.Models.FiniteTwoState

def stateIndicator : State → Int := fun s => if s = zero then 0 else 1

theorem generatorDriftAtZero :
    generatorAction twoStateGenerator stateIndicator zero = 1 := by decide

end Book.Chapters.Chapter58
