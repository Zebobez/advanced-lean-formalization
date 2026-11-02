module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 103 — Nonconvex Frank–Wolfe and Stationarity Certificates

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter103

open Book.Models.FiniteOptimization

def stationarityGap (x : Candidate) : Nat := if x = last then 0 else 1

theorem nonoptimal_candidates_have_positive_gap : stationarityGap first > 0 ∧ stationarityGap middle > 0 := by decide

theorem minimizer_has_zero_gap : stationarityGap last = 0 := by decide

end Book.Chapters.Chapter103
