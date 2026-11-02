module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 73 — Regeneration and Renewal Rewards

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter73

open Book.Models.FiniteTwoState

def cycleReward : Weight := fun s => if s = zero then 2 else 1
def cycleLength : Nat := totalWeight uniformWeight

theorem oneCycleReward : totalWeight cycleReward = 3 := by decide
theorem oneCycleLength : cycleLength = 2 := by decide

end Book.Chapters.Chapter73
