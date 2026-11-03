module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 98 — Frank–Wolfe and Projection-Free Optimization

Extracted from manuscript/chapters/part-23/chapter-98-frank-wolfe-and-projection-free-optimization.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter98

-- Source Lean fence 1

open Book.Models.FiniteOptimization

def linearMinimizer : Candidate := last
def frankWolfeGap (x : Candidate) : Nat := loss x - loss linearMinimizer

theorem frank_wolfe_gap_at_first : frankWolfeGap first = 4 := by decide

theorem frank_wolfe_gap_at_solution : frankWolfeGap linearMinimizer = 0 := by decide

structure LinearOracleCert {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (g s : E) : Prop where
  feasible : s ∈ X
  optimal : ∀ y, y ∈ X → inner ℝ g s ≤ inner ℝ g y

theorem frankWolfe_gap_nonnegative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {g x s : E} (hx : x ∈ X)
    (hcert : LinearOracleCert X g s) :
    0 ≤ inner ℝ g (x - s) := by
  have hopt := hcert.optimal x hx
  rw [inner_sub_right]
  linarith

theorem frankWolfe_gap_dominates_primal_error
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {f : E → ℝ} {g x xstar s : E}
    (hstar : xstar ∈ X) (hcert : LinearOracleCert X g s)
    (hsupport : f x - f xstar ≤ inner ℝ g (x - xstar)) :
    f x - f xstar ≤ inner ℝ g (x - s) := by
  calc
    f x - f xstar ≤ inner ℝ g (x - xstar) := hsupport
    _ ≤ inner ℝ g (x - s) := by
      have hopt := hcert.optimal xstar hstar
      rw [inner_sub_right, inner_sub_right]
      linarith

end Book.Chapters.Chapter98
