module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 71 — Quasi-Stationary Laws and Doob Transforms

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter71

open Book.Models.FiniteTwoState

def killedKernel : Kernel := fun i j =>
  if i = zero then (if j = zero then 1 else 0) else 0

theorem survivalMassAfterKilling : rowMass killedKernel zero = 1 := by decide

end Book.Chapters.Chapter71
