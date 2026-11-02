module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 74 — Martingale Approximations for Additive Functionals

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter74

open Book.Models.FiniteTwoState

def additiveIncrement : State → Int := fun s => if s = zero then -1 else 1

theorem centeredAdditiveFunctional :
    expectationNumerator uniformWeight additiveIncrement = 0 := by decide

end Book.Chapters.Chapter74
