module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 116 — Proximal Quasi-Newton Methods and Structured Metrics

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter116

open Book.Models.FiniteOptimization

def curvaturePairing (s y : Int) : Int := s * y

theorem positive_curvature_example : 0 < curvaturePairing 2 3 := by decide

theorem zero_step_has_zero_curvature : curvaturePairing 0 3 = 0 := by decide

end Book.Chapters.Chapter116
