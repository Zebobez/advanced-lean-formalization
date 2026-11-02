module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 49 — Metropolis–Hastings and Detailed Balance

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter49

open Book.Models.FiniteTwoState

def acceptProposal (proposal target : Nat) : Nat :=
  if proposal ≤ target then proposal else target

theorem symmetricMinimumAcceptsTheSmallerWeight : acceptProposal 2 1 = 1 := by decide

end Book.Chapters.Chapter49
