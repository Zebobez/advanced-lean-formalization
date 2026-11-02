module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 79 — Quasi-Birth–Death Processes and Matrix-Analytic Methods

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter79

open Book.Models.FiniteTwoState

def blockTransition : Kernel := resetKernel

theorem blockZeroRowHasUnitEntry : blockTransition zero zero = 1 := by decide
theorem blockRowMassIsTwo : rowMass blockTransition one = 2 := by decide

end Book.Chapters.Chapter79
