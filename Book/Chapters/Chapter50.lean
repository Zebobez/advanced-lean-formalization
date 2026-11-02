module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 50 — Gibbs Sampling and Conditional Kernels

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter50

open Book.Models.FiniteTwoState

theorem gibbsUpdateHasUniformRowAtZero : rowMass resetKernel zero = 2 :=
  reset_zero_row
theorem gibbsUpdateHasUniformRowAtOne : rowMass resetKernel one = 2 :=
  reset_one_row

end Book.Chapters.Chapter50
