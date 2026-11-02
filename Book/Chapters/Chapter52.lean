module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 52 — Variance and Monte Carlo Error Bounds

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter52

open Book.Models.FiniteTwoState

def centeredSample : State → Int := fun s => if s = zero then -1 else 1
def squaredSample (s : State) : Int := centeredSample s * centeredSample s

theorem bernoulliSampleHasZeroMean :
    expectationNumerator uniformWeight centeredSample = 0 := by decide
theorem bernoulliSampleHasSecondMomentTwo :
    expectationNumerator uniformWeight squaredSample = 2 := by decide

end Book.Chapters.Chapter52
