module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 87 — Monotone Construction of the Rate Matrix

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter87

open Book.Models.FiniteTwoState

def monotoneRateMap (n : Nat) : Nat := Nat.min (n + 1) 2

theorem rateMapAtZero : monotoneRateMap 0 = 1 := by decide
theorem rateMapAtCapacity : monotoneRateMap 2 = 2 := by decide

end Book.Chapters.Chapter87
