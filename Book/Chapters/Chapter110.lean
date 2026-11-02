module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 110 — ADMM, Augmented Lagrangians, and Residual Certificates

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter110

open Book.Models.FiniteOptimization

def constraintResidual (x y : Int) : Int := x - y
def augmentedEnergy (residual : Int) : Int := residual * residual

theorem feasible_pair_has_zero_residual : constraintResidual 2 2 = 0 := by decide

theorem augmented_energy_is_zero_at_feasibility : augmentedEnergy (constraintResidual 2 2) = 0 := by decide

end Book.Chapters.Chapter110
