module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 86 — Spectral Asymptotics of Matrix-Geometric Tails

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter86

open Book.Models.FiniteTwoState

def dominantMode (n : Nat) : Nat := 2 ^ n
def secondaryMode (n : Nat) : Nat := 1 ^ n

theorem dominantModeExceedsSecondaryAtThree : dominantMode 3 > secondaryMode 3 := by decide

end Book.Chapters.Chapter86
