module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 65 — Graph Laplacians and Effective Resistance

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter65

open Book.Models.FiniteTwoState

def neighbor (s : State) : State := if s = zero then one else zero
def contrastPotential : State → Int := fun s => if s = zero then 1 else -1
def graphLaplacian (s : State) : Int := contrastPotential s - contrastPotential (neighbor s)

theorem laplacianAtZero : graphLaplacian zero = 2 := by decide
theorem laplacianAtOne : graphLaplacian one = -2 := by decide

end Book.Chapters.Chapter65
