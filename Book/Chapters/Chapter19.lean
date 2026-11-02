module

public import Mathlib

public section

/-!
# Chapter 19 — Reflection and Certified Computation

Extracted from manuscript/chapters/part-03/chapter-19-reflection-and-certified-computation.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter19

-- Source Lean fence 1
example : 23 + 19 = 42 := by
  decide

example : 2 + 3 = 5 ∧ 10 < 20 := by
  decide

-- Source Lean fence 3
example : (List.range 1000).length = 1000 := by
  native_decide

-- Source Lean fence 5
example (x y : ℤ) : (x + y)^2 = x^2 + 2 * x * y + y^2 := by
  ring

example (m n : ℕ) (h : m ≤ n) : m + 1 ≤ n + 1 := by
  omega

end Book.Chapters.Chapter19
