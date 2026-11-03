module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 75 — Functional Central Limit Theorems

Extracted from manuscript/chapters/part-19/chapter-75-functional-central-limit-theorems.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter75

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def standardizedIncrement : State → Int := fun s => if s = zero then -1 else 1
def incrementSquare (s : State) : Int := standardizedIncrement s * standardizedIncrement s

theorem limitTheoremMeanCondition :
    expectationNumerator uniformWeight standardizedIncrement = 0 := by decide
theorem limitTheoremVarianceNumerator :
    expectationNumerator uniformWeight incrementSquare = 2 := by decide

-- Source Lean fence 3
theorem endpointCorrection_bound {S : Type} (h : S → ℝ) (B : ℝ)
    (x y : S) (hx : |h x| ≤ B) (hy : |h y| ≤ B) :
    |h y - h x| ≤ 2 * B := by
  calc
    |h y - h x| ≤ |h y| + |h x| := abs_sub _ _
    _ ≤ B + B := add_le_add hy hx
    _ = 2 * B := by ring

theorem pathEndpointCorrection_bound {S : Type} (h : S → ℝ) (B : ℝ)
    (path : ℝ → S) (hBound : ∀ t, |h (path t)| ≤ B) :
    ∀ t, |h (path t) - h (path 0)| ≤ 2 * B := by
  intro t
  exact endpointCorrection_bound h B (path 0) (path t)
    (hBound 0) (hBound t)

theorem scaledPathEndpointCorrection_bound {S : Type} (h : S → ℝ)
    (B T : ℝ) (path : ℝ → S) (hT : 0 < T)
    (hBound : ∀ t, |h (path t)| ≤ B) :
    ∀ t,
      |(h (path (T * t)) - h (path 0)) / Real.sqrt T| ≤
        (2 * B) / Real.sqrt T := by
  intro t
  have hroot : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  rw [abs_div, abs_of_pos hroot]
  exact div_le_div_of_nonneg_right
    (endpointCorrection_bound h B (path 0) (path (T * t))
      (hBound 0) (hBound (T * t)))
    (le_of_lt hroot)

end Book.Chapters.Chapter75
