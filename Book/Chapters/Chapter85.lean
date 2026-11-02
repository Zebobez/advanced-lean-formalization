module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 85 — Performance Measures from Matrix-Geometric Tails

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter85

open Book.Models.FiniteTwoState

def queueOccupancy : Weight := fun s => if s = zero then 0 else 1
def occupancyNumerator : Nat := totalWeight queueOccupancy

theorem finiteQueueOccupancy : occupancyNumerator = 1 := by decide

end Book.Chapters.Chapter85
