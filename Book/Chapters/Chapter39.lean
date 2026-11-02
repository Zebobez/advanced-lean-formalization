module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 39 — Predictable Processes and Doob Decomposition

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter39

open Book.Models.FiniteTwoState

def rawIncrement : State → Int := fun s => if s = zero then -1 else 1
def predictableDrift : State → Int := rawIncrement
def martingaleResidual (s : State) : Int := rawIncrement s - predictableDrift s

theorem residualAtZero : martingaleResidual zero = 0 := by decide
theorem residualAtOne : martingaleResidual one = 0 := by decide

end Book.Chapters.Chapter39
