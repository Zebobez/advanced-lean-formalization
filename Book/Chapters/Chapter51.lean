module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 51 — Importance Sampling and Change of Measure

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter51

open Book.Models.FiniteTwoState

def proposal : Weight := uniformWeight
def importanceLikelihood : Weight := fun s => if s = zero then 2 else 1
def weightedSample : Weight := fun s => proposal s * importanceLikelihood s

theorem importanceWeightNormalizer : totalWeight weightedSample = 3 := by decide
theorem weightedMassAtZero : weightedSample zero = 2 := by decide

end Book.Chapters.Chapter51
