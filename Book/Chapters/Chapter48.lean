module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 48 — Total Variation and Markov Chain Convergence

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter48

open Book.Models.FiniteTwoState

def pointMassZero : Weight := fun s => if s = zero then 1 else 0
def pointMassOne : Weight := fun s => if s = one then 1 else 0
def absoluteMassDifference (a b : Nat) : Nat := (a - b) + (b - a)
def totalVariationNumerator : Nat :=
  absoluteMassDifference (pointMassZero zero) (pointMassOne zero) +
  absoluteMassDifference (pointMassZero one) (pointMassOne one)

theorem distinctPointMassesHaveDistanceTwo : totalVariationNumerator = 2 := by decide

end Book.Chapters.Chapter48
