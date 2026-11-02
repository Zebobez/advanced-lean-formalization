module

public import Book.Models.FiniteOptimization
public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 104 — Stochastic Frank–Wolfe and Noisy Linear Oracles

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter104

open Book.Models.FiniteOptimization
open Book.Models.FiniteTwoState

def stochasticOracleNoise : State → Int := fun s => if s = zero then -2 else 2

theorem stochastic_oracle_is_unbiased : expectationNumerator uniformWeight stochasticOracleNoise = 0 := by decide

end Book.Chapters.Chapter104
