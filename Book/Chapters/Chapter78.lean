module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 78 — Aggregation and Singular Perturbation of Markov Chains

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter78

open Book.Models.FiniteTwoState

def aggregateToOneClass (_s : State) : Nat := 0

theorem aggregationErasesTheWithinClassLabel :
    aggregateToOneClass zero = aggregateToOneClass one := by decide

end Book.Chapters.Chapter78
