module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 91 — Smooth Convex Optimization and Gradient Descent

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter91

open Book.Models.FiniteOptimization

theorem gradient_step_decreases_from_first : loss (gradientStep first) < loss first := by decide

theorem gradient_step_reaches_minimum_from_middle : gradientStep middle = last := by decide

end Book.Chapters.Chapter91
