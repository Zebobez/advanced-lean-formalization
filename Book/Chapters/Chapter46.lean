module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 46 — Measure-Preserving Dynamics and Ergodicity

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter46

open Book.Models.FiniteTwoState

def rotation (s : State) : State := if s = zero then one else zero
def rotatedUniformMass (s : State) : Nat := uniformWeight (rotation s)

theorem rotationPreservesMassAtZero : rotatedUniformMass zero = 1 := by decide
theorem rotationPreservesMassAtOne : rotatedUniformMass one = 1 := by decide

end Book.Chapters.Chapter46
