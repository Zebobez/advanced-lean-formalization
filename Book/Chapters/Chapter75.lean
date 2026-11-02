module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 75 — Functional Central Limit Theorems

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter75

open Book.Models.FiniteTwoState

def standardizedIncrement : State → Int := fun s => if s = zero then -1 else 1
def incrementSquare (s : State) : Int := standardizedIncrement s * standardizedIncrement s

theorem limitTheoremMeanCondition :
    expectationNumerator uniformWeight standardizedIncrement = 0 := by decide
theorem limitTheoremVarianceNumerator :
    expectationNumerator uniformWeight incrementSquare = 2 := by decide

end Book.Chapters.Chapter75
