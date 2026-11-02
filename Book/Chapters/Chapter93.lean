module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 93 — Estimate Sequences and Accelerated Gradient

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter93

open Book.Models.FiniteOptimization

def estimateWeight (k : Nat) : Nat := (k + 1) * loss last

theorem estimate_sequence_vanishes_at_minimizer : ∀ k, estimateWeight k = 0 := by intro k; simp [estimateWeight, loss, last]

end Book.Chapters.Chapter93
