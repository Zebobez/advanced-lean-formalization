module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 53 — Sequential Importance Sampling and Filtering

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter53

open Book.Models.FiniteTwoState

def firstLikelihood : Weight := fun s => if s = zero then 2 else 1
def secondLikelihood : Weight := fun _ => 1
def sequentialWeight : Weight := fun s => firstLikelihood s * secondLikelihood s

theorem oneStepFilterNormalizer : totalWeight sequentialWeight = 3 := by decide

end Book.Chapters.Chapter53
