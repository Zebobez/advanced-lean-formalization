module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 47 — Ergodic Averages and Empirical Measures

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter47

open Book.Models.FiniteTwoState

def orbitObservable : State → Int := fun s => if s = zero then 0 else 2

theorem twoPointOrbitAverageNumerator :
    expectationNumerator uniformWeight orbitObservable = 2 := by decide

end Book.Chapters.Chapter47
