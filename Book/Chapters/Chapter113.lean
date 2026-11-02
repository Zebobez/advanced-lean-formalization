module

public import Mathlib

public section

/-!
# Chapter 113 — Forward–Backward Splitting and Cocoercive Operators

Extracted from manuscript/chapters/part-23/chapter-113-forward-backward-splitting.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter113

-- Source Lean fence 2
structure CocoerciveMap (H : Type*) [SeminormedAddCommGroup H] [InnerProductSpace ℝ H] where
  toFun : H → H
  beta : ℝ
  beta_pos : 0 < beta
  cocoercive : ∀ x y,
    beta * ‖toFun x - toFun y‖ ^ 2 ≤
      inner ℝ (toFun x - toFun y) (x - y)

def ResolventSpec {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → H → Prop) (gamma : ℝ)
    (v x : H) : Prop :=
  0 < gamma ∧ A x (gamma⁻¹ • (v - x))

end Book.Chapters.Chapter113
