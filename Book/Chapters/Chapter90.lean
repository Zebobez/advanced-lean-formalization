module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 90 — Convexity, Subgradients, and Optimality Certificates

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter90

open Book.Models.FiniteOptimization

theorem last_is_global_minimum : ∀ x : Candidate, loss last ≤ loss x := by decide

theorem first_optimality_gap_is_four : objectiveGap first = 4 := by decide

end Book.Chapters.Chapter90
