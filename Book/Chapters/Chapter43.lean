module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 43 — Conditional Independence

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter43

open Book.Models.FiniteTwoState

def independentJoint : Kernel := resetKernel

theorem everyIndependentCellHasUnitWeight : independentJoint zero zero = 1 := by decide
theorem secondIndependentCellHasUnitWeight : independentJoint one zero = 1 := by decide

end Book.Chapters.Chapter43
