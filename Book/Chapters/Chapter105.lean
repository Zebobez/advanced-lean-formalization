module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 105 — Finite-Sum Frank–Wolfe: Variance Reduction and Gap Estimation

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter105

open Book.Models.FiniteOptimization

def componentLoss (i x : Candidate) : Nat := if i = first then loss x else if i = middle then x.val else 2 - x.val
def finiteSumNumerator (x : Candidate) : Nat := componentLoss first x + componentLoss middle x + componentLoss last x

theorem finite_sum_at_solution : finiteSumNumerator last = 2 := by decide

theorem finite_sum_at_first : finiteSumNumerator first = 6 := by decide

end Book.Chapters.Chapter105
