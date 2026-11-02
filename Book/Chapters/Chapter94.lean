module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 94 — Mirror Descent and Bregman Geometry

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter94

open Book.Models.FiniteOptimization

def bregmanSquare (x y : Int) : Int := (x - y) * (x - y)

theorem bregman_example_value : bregmanSquare 3 1 = 4 := by decide

theorem bregman_equal_points_vanish (x : Int) : bregmanSquare x x = 0 := by simp [bregmanSquare]

end Book.Chapters.Chapter94
