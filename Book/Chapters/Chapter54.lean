module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 54 — Resampling and Particle Systems

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter54

open Book.Models.FiniteTwoState

def resampledCount : Weight := fun s => if s = zero then 2 else 0

theorem resamplingPreservesPopulationSize : totalWeight resampledCount = 2 := by decide
theorem allCopiesMayCoincide : resampledCount zero = 2 := by decide

end Book.Chapters.Chapter54
