module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 55 — Finite-State Continuous-Time Markov Chains

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter55

open Book.Models.FiniteTwoState

theorem generatorConservesMassAtZero : generatorRowSum twoStateGenerator zero = 0 :=
  generator_zero_row
theorem generatorConservesMassAtOne : generatorRowSum twoStateGenerator one = 0 :=
  generator_one_row

end Book.Chapters.Chapter55
