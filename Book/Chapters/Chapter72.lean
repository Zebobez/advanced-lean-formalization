module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 72 — Resolvents and Green Kernels

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter72

open Book.Models.FiniteTwoState

def truncatedGreenMass : Nat :=
  rowMass identityKernel zero + rowMass flipKernel zero

theorem twoTermGreenCalculation : truncatedGreenMass = 4 := by decide

end Book.Chapters.Chapter72
