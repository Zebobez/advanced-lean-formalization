module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 115 — Variable-Metric Forward–Backward Splitting

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter115

open Book.Models.FiniteOptimization

def metricEnergy (x : Int) (weight : Nat) : Int := Int.ofNat weight * x * x

theorem positive_metric_gives_positive_energy : 0 < metricEnergy 2 3 := by decide

theorem zero_displacement_has_zero_energy (weight : Nat) : metricEnergy 0 weight = 0 := by simp [metricEnergy]

end Book.Chapters.Chapter115
