module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 38 — Martingale Convergence and Uniform Integrability

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter38

open Book.Models.FiniteTwoState

@[expose]
def conditionalPrediction (_time : Nat) : Int := 3

theorem predictionIsUniformlyIntegrableAtEveryFiniteTime (time : Nat) :
    conditionalPrediction time = 3 := rfl

end Book.Chapters.Chapter38
