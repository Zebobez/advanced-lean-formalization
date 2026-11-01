module

import Mathlib.Data.Nat.Basic

/-!
# Smoke-test module

This is a small compilation check, not the textbook's actual first chapter.
Use a focused Mathlib import to avoid loading the entire library into memory.
-/

namespace Book.Chapter01

example (n : ℕ) : n + 0 = n := by
  simp

end Book.Chapter01
