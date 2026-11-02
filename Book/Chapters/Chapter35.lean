module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 35 — Conditional Expectation and Information

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter35

open Book.Models.FiniteTwoState

def eventMass : Weight := fun s => if s = zero then 1 else 0
def observedPayoff : State → Int := fun s => if s = zero then 0 else 2

theorem oneAtomPartition : totalWeight eventMass = 1 := by decide
theorem conditionalPayoffNumerator :
    expectationNumerator uniformWeight observedPayoff = 2 := by decide

end Book.Chapters.Chapter35
