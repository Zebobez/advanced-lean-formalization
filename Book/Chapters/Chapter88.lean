module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 88 — Newton Linearization for Matrix Rate Equations

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter88

open Book.Models.FiniteTwoState

def scalarRateResidual (x : Nat) : Nat := x * x - 1

theorem unitRateIsAnExactRoot : scalarRateResidual 1 = 0 := by decide

end Book.Chapters.Chapter88
