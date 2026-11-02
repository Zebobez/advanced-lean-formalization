module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 83 — M/G/1-Type Chains and Batch Arrivals

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter83

open Book.Models.FiniteTwoState

def batchArrival (level batch : Nat) : Nat := level + batch

theorem batchArrivalAddsTwoCustomers : batchArrival 1 2 = 3 := by decide

end Book.Chapters.Chapter83
