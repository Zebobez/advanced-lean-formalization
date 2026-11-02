module

public import Book.Models.FiniteOptimization
public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 95 — Stochastic Gradient Methods and Expected Guarantees

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter95

open Book.Models.FiniteOptimization
open Book.Models.FiniteTwoState

def sampledNoise : State → Int := fun s => if s = zero then -1 else 1

theorem sampled_noise_has_zero_mean : expectationNumerator uniformWeight sampledNoise = 0 := by decide

end Book.Chapters.Chapter95
