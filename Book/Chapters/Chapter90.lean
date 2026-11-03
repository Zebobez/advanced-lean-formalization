module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 90 — Convexity, Subgradients, and Optimality Certificates

Extracted from manuscript/chapters/part-23/chapter-90-convexity-subgradients-and-optimality-certificates.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter90

-- Source Lean fence 1

open Book.Models.FiniteOptimization

theorem last_is_global_minimum : ∀ x : Candidate, loss last ≤ loss x := by decide

theorem first_optimality_gap_is_four : objectiveGap first = 4 := by decide

def IsSubgradientAt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (f : E → ℝ) (x g : E) : Prop :=
  x ∈ C ∧ ∀ y ∈ C,
    f x + inner ℝ g (y - x) ≤ f y

theorem zero_subgradient_is_minimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {f : E → ℝ} {x : E}
    (h : IsSubgradientAt C f x 0) :
    x ∈ C ∧ ∀ y ∈ C, f x ≤ f y := by
  rcases h with ⟨hx, hs⟩
  refine ⟨hx, fun y hy => ?_⟩
  simpa using hs y hy

theorem subgradient_add
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {f₁ f₂ : E → ℝ} {x g₁ g₂ : E}
    (h₁ : IsSubgradientAt C f₁ x g₁)
    (h₂ : IsSubgradientAt C f₂ x g₂) :
    IsSubgradientAt C (fun z => f₁ z + f₂ z) x (g₁ + g₂) := by
  rcases h₁ with ⟨hx, h₁⟩
  rcases h₂ with ⟨_, h₂⟩
  refine ⟨hx, fun y hy => ?_⟩
  change (f₁ x + f₂ x) + inner ℝ (g₁ + g₂) (y - x) ≤ f₁ y + f₂ y
  rw [inner_add_left]
  have hsum := add_le_add (h₁ y hy) (h₂ y hy)
  linarith

end Book.Chapters.Chapter90
