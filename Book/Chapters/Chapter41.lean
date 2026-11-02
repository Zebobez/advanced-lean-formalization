module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 41 — Disintegration and Conditional Kernels

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter41

open Book.Models.FiniteTwoState

def conditionalTable : Kernel := resetKernel
def observedMarginalAtZero : Nat := conditionalTable zero zero + conditionalTable one zero

theorem conditionalTableCell : conditionalTable zero one = 1 := by decide
theorem observedMarginal : observedMarginalAtZero = 2 := by decide

end Book.Chapters.Chapter41
