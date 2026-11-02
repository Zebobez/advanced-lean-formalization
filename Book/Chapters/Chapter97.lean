module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 97 — Adaptive Subgradients and AdaGrad

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter97

open Book.Models.FiniteOptimization

def accumulatedSquares : Nat := 3 * 3 + 4 * 4

theorem adagrad_accumulator_example : accumulatedSquares = 25 := by decide

theorem accumulator_is_nonnegative : 0 ≤ accumulatedSquares := by omega

end Book.Chapters.Chapter97
