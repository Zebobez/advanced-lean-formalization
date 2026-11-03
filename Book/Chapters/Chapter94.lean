module

public import Book.Models.FiniteOptimization
public import Mathlib

public section

/-!
# Chapter 94 — Mirror Descent and Bregman Geometry

Extracted from manuscript/chapters/part-23/chapter-94-mirror-descent-and-bregman-geometry.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter94

-- Source Lean fence 1

open Book.Models.FiniteOptimization

def bregmanSquare (x y : Int) : Int := (x - y) * (x - y)

theorem bregman_example_value : bregmanSquare 3 1 = 4 := by decide

theorem bregman_equal_points_vanish (x : Int) : bregmanSquare x x = 0 := by simp [bregmanSquare]

def BregmanDiv {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (psi : E → ℝ) (gradPsi : E → E) (x y : E) : ℝ :=
  psi x - psi y - inner ℝ (gradPsi y) (x - y)

theorem bregman_three_point_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (psi : E → ℝ) (gradPsi : E → E) (u x p : E) :
    BregmanDiv psi gradPsi u x - BregmanDiv psi gradPsi u p -
        BregmanDiv psi gradPsi p x =
      inner ℝ (gradPsi p - gradPsi x) (u - p) := by
  unfold BregmanDiv
  have hux : u - x = (u - p) + (p - x) := by abel
  rw [hux, inner_add_right, inner_sub_left]
  ring

end Book.Chapters.Chapter94
