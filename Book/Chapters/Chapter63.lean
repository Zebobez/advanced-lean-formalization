module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 63 — Birth–Death Chains and Hitting Problems

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter63

open Book.Models.FiniteTwoState

theorem birthRateFromZero : twoStateGenerator zero one = 1 := by decide
theorem deathRateFromOne : twoStateGenerator one zero = 2 := by decide
theorem birthDeathRowBalance :
    generatorRowSum twoStateGenerator zero = 0 := generator_zero_row

end Book.Chapters.Chapter63
