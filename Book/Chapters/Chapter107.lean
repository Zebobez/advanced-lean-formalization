module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 107 — Nonconvex Stationarity with Cached Frank–Wolfe Gradients

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter107

open Book.Models.FiniteOptimization

def cacheAgeError (age : Nat) : Nat := age
def cacheErrorBound (age : Nat) : Nat := 2 * age

theorem cache_error_bound_holds (age : Nat) : cacheAgeError age ≤ cacheErrorBound age := by unfold cacheAgeError cacheErrorBound; omega

theorem fresh_cache_has_zero_error : cacheAgeError 0 = 0 := by decide

end Book.Chapters.Chapter107
