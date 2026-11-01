import Mathlib

/-!
# Smoke-test module

This file confirms that the project can import Mathlib and compile a Lean proof.
It is **not** content for Chapter 1 of the textbook.
-/

namespace Book.Chapter01

example (n : ℕ) : n + 0 = n := by
  simp

end Book.Chapter01
