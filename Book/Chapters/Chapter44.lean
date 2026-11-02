module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 44 — Irreducible Markov Kernels

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter44

open Book.Models.FiniteTwoState

theorem zeroCanReachOne : 0 < flipKernel zero one := by decide
theorem oneCanReachZero : 0 < flipKernel one zero := by decide

end Book.Chapters.Chapter44
