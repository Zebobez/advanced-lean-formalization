module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 114 — Backtracking Proximal Gradient and Local Curvature Certificates

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter114

open Book.Models.FiniteOptimization

def backtrackingBound (x : Candidate) : Nat := loss x
def acceptedStepValue (x : Candidate) : Nat := loss (gradientStep x)

theorem backtracking_accepts_decreasing_step : acceptedStepValue first < backtrackingBound first := by decide

theorem accepted_step_reaches_minimum : acceptedStepValue middle = 0 := by decide

end Book.Chapters.Chapter114
