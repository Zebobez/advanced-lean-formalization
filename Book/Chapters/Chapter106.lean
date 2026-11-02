module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 106 — Structured Gap Estimation for Generalized Linear Frank–Wolfe

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter106

open Book.Models.FiniteOptimization

def structuredGapEstimate (x : Candidate) : Nat := objectiveGap x
def certifiedGapUpperBound (x : Candidate) : Nat := if x = first then 4 else 1

theorem structured_gap_is_bounded_at_first : structuredGapEstimate first ≤ certifiedGapUpperBound first := by decide

theorem structured_gap_is_zero_at_solution : structuredGapEstimate last = 0 := by decide

end Book.Chapters.Chapter106
