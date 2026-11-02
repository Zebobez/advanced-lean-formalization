module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 61 — Time-Inhomogeneous Chains and Evolution Families

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter61

open Book.Models.FiniteTwoState

theorem identityThenFlipTransition : composeAt identityKernel flipKernel zero one = 2 := by decide
theorem flipThenIdentityTransition : composeAt flipKernel identityKernel zero one = 2 := by decide

end Book.Chapters.Chapter61
