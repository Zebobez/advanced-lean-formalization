module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 92 — Projected Gradient and Proximal Methods

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter92

open Book.Models.FiniteOptimization

theorem projected_step_keeps_first_feasible : projectedStep first = first := by decide

theorem projected_step_reaches_minimum_from_middle : projectedStep middle = last := by decide

end Book.Chapters.Chapter92
