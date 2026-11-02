module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 77 — Averaging for Fast–Slow Markov Chains

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter77

open Book.Models.FiniteTwoState

def fastDrift : State → Int := fun s => if s = zero then -1 else 1

theorem averagedFastDriftIsZero :
    expectationNumerator uniformWeight fastDrift = 0 := by decide

end Book.Chapters.Chapter77
