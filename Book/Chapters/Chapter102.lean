module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 102 — Frank–Wolfe over Strongly Convex Sets

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter102

open Book.Models.FiniteOptimization

def discreteCurvature : Int := Int.ofNat (loss first + loss last) - 2 * Int.ofNat (loss middle)

theorem discrete_curvature_is_positive : 0 < discreteCurvature := by decide

end Book.Chapters.Chapter102
