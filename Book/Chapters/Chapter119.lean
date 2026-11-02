module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 119 — Local Superlinear Convergence and Forcing Terms

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter119

open Book.Models.FiniteOptimization

def localError (k : Nat) : Nat := if k = 0 then 4 else if k = 1 then 1 else 0

theorem local_error_reaches_zero : localError 2 = 0 := by decide

theorem later_error_remains_zero (k : Nat) (hk : 2 ≤ k) : localError k = 0 := by
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  simp [localError, h0, h1]

end Book.Chapters.Chapter119
