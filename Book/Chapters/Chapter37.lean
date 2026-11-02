module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 37 — Stopping Times and Optional Sampling

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter37

open Book.Models.FiniteTwoState

def stoppedPosition : State → Nat := fun s => if s = zero then 0 else 1

theorem stopAtLowerState : stoppedPosition zero = 0 := by decide
theorem stopAtUpperState : stoppedPosition one = 1 := by decide

end Book.Chapters.Chapter37
