module

public import Book.Models.FiniteOptimization
public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 96 — Control Variates and Finite-Sum Variance Reduction

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter96

open Book.Models.FiniteOptimization
open Book.Models.FiniteTwoState

def rawGradientSample : State → Int := fun s => if s = zero then 2 else 4
def baselineGradientSample : State → Int := fun s => if s = zero then 1 else 3
def snapshotGradient : Int := 2
def correctedSample (s : State) : Int := rawGradientSample s - baselineGradientSample s + snapshotGradient

theorem corrected_sample_is_constant : ∀ s, correctedSample s = 3 := by decide

theorem corrected_sample_variance_numerator : expectationNumerator uniformWeight (fun s => correctedSample s - 3) = 0 := by decide

end Book.Chapters.Chapter96
