module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 45 — Invariant and Reversible Markov Kernels

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter45

open Book.Models.FiniteTwoState

theorem uniformLawIsInvariantAtZero : invariantAt uniformWeight flipKernel zero :=
  uniform_flip_invariant_zero
theorem uniformLawSatisfiesDetailedBalance :
    detailedBalanceAt uniformWeight flipKernel zero one := uniform_flip_detailed_balance

end Book.Chapters.Chapter45
