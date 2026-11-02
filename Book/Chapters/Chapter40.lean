module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 40 — Markov Kernels and Transition Systems

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter40

open Book.Models.FiniteTwoState

theorem transitionRowsHaveMassTwoAtZero : rowMass identityKernel zero = 2 :=
  identity_zero_row
theorem transitionRowsHaveMassTwoAtOne : rowMass identityKernel one = 2 :=
  identity_one_row

end Book.Chapters.Chapter40
