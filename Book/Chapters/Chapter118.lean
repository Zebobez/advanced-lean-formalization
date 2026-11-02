module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 118 — Global Convergence of Proximal Newton Iterations

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter118

open Book.Models.FiniteOptimization

def proximalNewtonCandidate : Candidate := gradientStep middle

theorem proximal_newton_example_decreases_objective : loss proximalNewtonCandidate < loss first := by decide

theorem proximal_newton_candidate_is_optimal : proximalNewtonCandidate = last := by decide

end Book.Chapters.Chapter118
