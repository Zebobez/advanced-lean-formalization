module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 76 — Population Scaling and Diffusion Limits

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter76

open Book.Models.FiniteTwoState

def populationCount : State → Nat := fun s => if s = zero then 0 else 1
def scaledPopulation (s : State) : Nat := 2 * populationCount s

theorem scalingPreservesTheZeroState : scaledPopulation zero = 0 := by decide
theorem scalingOfOneIndividual : scaledPopulation one = 2 := by decide

end Book.Chapters.Chapter76
