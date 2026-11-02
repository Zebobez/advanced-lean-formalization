module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 101 — Pairwise Frank–Wolfe and Sparse Support Transfers

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter101

open Book.Models.FiniteOptimization

theorem pairwise_update_conserves_mass :
    pairMass (transferOne 2 1).1 (transferOne 2 1).2 = pairMass 2 1 := by decide

theorem pairwise_update_stays_nonnegative : (transferOne 2 1).1 ≥ 0 := by decide

end Book.Chapters.Chapter101
