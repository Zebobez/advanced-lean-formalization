module

public import Mathlib

public section

/-!
# Chapter 14 — Finding and Reusing Library Theorems

Extracted from manuscript/chapters/part-02/chapter-14-library-search.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter14

-- Source Lean fence 1
#check Nat.add_comm
#check MonoidHom.map_mul

-- Source Lean fence 2
#print Nat.add_comm

-- Source Lean fence 3
example (i j k : Nat) (h₁ : i < j) (h₂ : j < k) : i < k := by
  exact?

-- Source Lean fence 4
#check MonoidHom.map_mul

-- Source Lean fence 5
example {M N : Type _} [Monoid M] [Monoid N]
    (f : M →* N) (a b : M) : f (a * b) = f a * f b := by
  exact map_mul f a b

-- Source Lean fence 6
example (i j k : Nat) (h₁ : i < j) (h₂ : j < k) : i < k := by
  exact Nat.lt_trans h₁ h₂

end Book.Chapters.Chapter14
