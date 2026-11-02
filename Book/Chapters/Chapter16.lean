module

public import Mathlib

public section

/-!
# Chapter 16 — Elaboration, Performance, and Proof Maintenance

Extracted from manuscript/chapters/part-02/chapter-16-elaboration-and-maintenance.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter16

-- Source Lean fence 2
example : (3 : Int) + 4 = 7 := by
  norm_num

-- Source Lean fence 3
example (n : Nat) : n + 1 ≤ n + 3 := by
  omega

end Book.Chapters.Chapter16
