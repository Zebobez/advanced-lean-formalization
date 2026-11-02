module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 120 — Kurdyka–Łojasiewicz Convergence and Finite Length

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter120

open Book.Models.FiniteOptimization

def klResidual (k : Nat) : Nat := 2 ^ k
def finiteLengthBound (n : Nat) : Nat := 2 ^ (n + 1) - 1

theorem kl_geometric_partial_sum_example : 1 + 2 + 4 + 8 = finiteLengthBound 3 := by decide

theorem kl_residual_is_positive (k : Nat) : 0 < klResidual k := by exact Nat.pow_pos (by decide)

end Book.Chapters.Chapter120
