module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 111 — Dykstra’s Algorithm and Projection onto Intersections

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter111

open Book.Models.FiniteOptimization

def projectNonnegative (x : Int) : Int := if x < 0 then 0 else x
def projectUnitInterval (x : Int) : Int := if x < 0 then 0 else if x > 1 then 1 else x

theorem dykstra_projection_clips_below_zero : projectUnitInterval (-3) = 0 := by decide

theorem dykstra_projection_clips_above_one : projectUnitInterval 4 = 1 := by decide

theorem projection_keeps_in_interval (x : Int) : 0 ≤ projectUnitInterval x ∧ projectUnitInterval x ≤ 1 := by
  by_cases hx0 : x < 0
  · simp [projectUnitInterval, hx0]
  · by_cases hx1 : x > 1
    · simp [projectUnitInterval, hx0, hx1]
    · simp [projectUnitInterval, hx0, hx1] <;> omega

end Book.Chapters.Chapter111
