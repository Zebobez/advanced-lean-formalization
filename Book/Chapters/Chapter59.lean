module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 59 — Feynman–Kac Semigroups and Killing

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter59

open Book.Models.FiniteTwoState

def killingPotential : State → Nat := fun _ => 1
def killedFlipWeight (i j : State) : Nat := killingPotential i * flipKernel i j

theorem constantKillingLeavesTheOffDiagonalWeight : killedFlipWeight zero one = 2 := by decide

end Book.Chapters.Chapter59
