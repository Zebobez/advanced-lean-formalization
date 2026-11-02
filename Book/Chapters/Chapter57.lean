module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 57 — Sample Paths and Non-Explosion

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter57

open Book.Models.FiniteTwoState

def alternatingPath (time : Nat) : State := if time % 2 = 0 then zero else one

theorem pathStartsAtZero : alternatingPath 0 = zero := by decide
theorem pathMovesToOne : alternatingPath 1 = one := by decide

end Book.Chapters.Chapter57
