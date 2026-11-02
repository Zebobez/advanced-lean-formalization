module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 100 — Fully Corrective Frank–Wolfe and Active-Set Optimization

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter100

open Book.Models.FiniteOptimization

def correctedWeights : Candidate → Nat := fun x => if x = last then 1 else 0
def totalCorrectedWeight : Nat := correctedWeights first + correctedWeights middle + correctedWeights last

theorem fully_corrective_weights_are_normalized : totalCorrectedWeight = 1 := by decide

theorem fully_corrective_support_contains_minimizer : correctedWeights last = 1 := by decide

end Book.Chapters.Chapter100
