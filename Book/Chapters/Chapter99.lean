module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 99 — Away-Step Frank–Wolfe and Linear Convergence

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter99

open Book.Models.FiniteOptimization

theorem away_step_preserves_pair_mass :
    pairMass (transferOne 1 1).1 (transferOne 1 1).2 = 2 := by decide

theorem away_step_removes_one_unit_from_donor : (transferOne 2 1).1 = 1 := by decide

end Book.Chapters.Chapter99
