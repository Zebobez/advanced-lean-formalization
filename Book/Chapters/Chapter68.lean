module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 68 — The Markov Chain Tree Theorem

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter68

open Book.Models.FiniteTwoState

def treeWeightAtZero : Nat := 2
def treeWeightAtOne : Nat := 1

theorem incomingTreeWeightsBalance : treeWeightAtZero * 1 = treeWeightAtOne * 2 := by decide

end Book.Chapters.Chapter68
