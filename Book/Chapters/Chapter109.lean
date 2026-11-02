module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 109 — Primal–Dual Hybrid Gradient and Proximal Splitting

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter109

open Book.Models.FiniteOptimization

def primalDualResidual (x y : Int) : Int := residual x y

theorem primal_dual_fixed_point_has_zero_residual : primalDualResidual 2 2 = 0 := by decide

theorem residual_detects_mismatch : primalDualResidual 3 1 = 2 := by decide

end Book.Chapters.Chapter109
