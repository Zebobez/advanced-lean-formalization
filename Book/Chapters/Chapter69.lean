module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 69 — Linear Response for Finite Markov Chains

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter69

open Book.Models.FiniteTwoState

def stationaryMass (parameter : Nat) : Nat := parameter + 1
def finiteResponse (base perturbation : Nat) : Nat :=
  stationaryMass (base + perturbation) - stationaryMass base

theorem unitPerturbationResponse : finiteResponse 1 1 = 1 := by decide

end Book.Chapters.Chapter69
