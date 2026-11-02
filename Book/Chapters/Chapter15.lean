module

public import Mathlib

public section

/-!
# Chapter 15 — Namespaces, Modules, and Typeclass Instances

Extracted from manuscript/chapters/part-02/chapter-15-library-organization.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter15

-- Source Lean fence 1
namespace FormalTools.Algebra

variable {M : Type _} [Monoid M]

def cube (x : M) : M := x * x * x

theorem cube_one : cube (1 : M) = 1 := by
  simp [cube]

end FormalTools.Algebra

-- Source Lean fence 2
namespace FormalTools.Algebra

section

variable {M : Type _} [Monoid M]

theorem cube_mul_one (x : M) : cube x * 1 = cube x := by
  simp [cube]

end
end FormalTools.Algebra

-- Source Lean fence 4
#synth Monoid Nat

example : Monoid Nat := by
  infer_instance

end Book.Chapters.Chapter15
