module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 112 — Douglas–Rachford Splitting and Monotone Inclusions

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter112

open Book.Models.FiniteOptimization

def reflectAtZero (x : Int) : Int := -x
def douglasRachfordStep (x : Int) : Int := (x + reflectAtZero x) / 2

theorem douglas_rachford_fixed_point : douglasRachfordStep 3 = 0 := by decide

theorem zero_is_fixed : douglasRachfordStep 0 = 0 := by decide

end Book.Chapters.Chapter112
