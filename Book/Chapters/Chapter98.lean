module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 98 — Frank–Wolfe and Projection-Free Optimization

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter98

open Book.Models.FiniteOptimization

def linearMinimizer : Candidate := last
def frankWolfeGap (x : Candidate) : Nat := loss x - loss linearMinimizer

theorem frank_wolfe_gap_at_first : frankWolfeGap first = 4 := by decide

theorem frank_wolfe_gap_at_solution : frankWolfeGap linearMinimizer = 0 := by decide

end Book.Chapters.Chapter98
