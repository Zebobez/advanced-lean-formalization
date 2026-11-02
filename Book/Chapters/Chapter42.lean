module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 42 — Bayesian Updating and Posterior Kernels

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter42

open Book.Models.FiniteTwoState

def prior : Weight := uniformWeight
def likelihood : Weight := fun s => if s = zero then 2 else 1
def posteriorWeight : Weight := fun s => prior s * likelihood s

theorem bayesNormalizer : totalWeight posteriorWeight = 3 := by decide
theorem posteriorFavorsZero : posteriorWeight zero = 2 := by decide

end Book.Chapters.Chapter42
