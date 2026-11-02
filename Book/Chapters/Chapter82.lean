module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 82 — Phase-Type Service and MAP/PH/1 Queues

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter82

open Book.Models.FiniteTwoState

def servicePhaseMass : Weight := uniformWeight
def absorptionMass : Weight := fun s => if s = one then 1 else 0

theorem twoPhaseMass : totalWeight servicePhaseMass = 2 := by decide
theorem oneAbsorbingPhase : totalWeight absorptionMass = 1 := by decide

end Book.Chapters.Chapter82
