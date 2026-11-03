module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 95 — Stochastic Gradient Methods and Expected Guarantees

Extracted from manuscript/chapters/part-23/chapter-95-stochastic-gradient-methods-and-expected-guarantees.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter95

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def sampledNoise : State → Int := fun s => if s = zero then -1 else 1

theorem sampled_noise_has_zero_mean :
    expectationNumerator uniformWeight sampledNoise = 0 := by decide

theorem sampled_noise_second_moment :
    expectationNumerator uniformWeight (fun s => sampledNoise s ^ 2) = 2 := by decide

theorem sampled_noise_variance_is_one :
    ((expectationNumerator uniformWeight (fun s => sampledNoise s ^ 2) : Int) : ℚ) / 2 -
      (((expectationNumerator uniformWeight sampledNoise : Int) : ℚ) / 2) ^ 2 = 1 := by
  rw [sampled_noise_second_moment, sampled_noise_has_zero_mean]
  norm_num

end Book.Chapters.Chapter95
