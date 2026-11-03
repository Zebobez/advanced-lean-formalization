module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 49 — Metropolis–Hastings and Detailed Balance

Extracted from manuscript/chapters/part-09/chapter-49-metropolis-hastings-and-detailed-balance.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter49

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def acceptProposal (proposal target : Nat) : Nat :=
  if proposal ≤ target then proposal else target

theorem symmetricMinimumAcceptsTheSmallerWeight : acceptProposal 2 1 = 1 := by decide

-- Source Lean fence 2
theorem exercise_49_3_weighted_acceptance_flow
    (wx wy qxy qyx : ℝ) (hwx : 0 < wx) :
    wx * min qxy (wy * qyx / wx) = min (wx * qxy) (wy * qyx) := by
  calc
    wx * min qxy (wy * qyx / wx) =
        min (wx * qxy) (wx * (wy * qyx / wx)) := by
      rw [mul_min_of_nonneg qxy (wy * qyx / wx) hwx.le]
    _ = min (wx * qxy) (wy * qyx) := by
      congr 1
      field_simp

theorem exercise_49_3_weighted_flow_symmetric
    (wx wy qxy qyx : ℝ) (hwx : 0 < wx) (hwy : 0 < wy) :
    wx * min qxy (wy * qyx / wx) = wy * min qyx (wx * qxy / wy) := by
  calc
    wx * min qxy (wy * qyx / wx) = min (wx * qxy) (wy * qyx) :=
      exercise_49_3_weighted_acceptance_flow wx wy qxy qyx hwx
    _ = min (wy * qyx) (wx * qxy) := min_comm _ _
    _ = wy * min qyx (wx * qxy / wy) :=
      (exercise_49_3_weighted_acceptance_flow wy wx qyx qxy hwy).symm

def mhAcceptanceRational (wx wy qxy qyx : ℚ) : ℚ :=
  min qxy (wy * qyx / wx)

theorem exercise_49_4_forward_acceptance :
    mhAcceptanceRational 1 3 1 1 = 1 := by
  norm_num [mhAcceptanceRational]

theorem exercise_49_4_reverse_acceptance :
    mhAcceptanceRational 3 1 1 1 = 1 / 3 := by
  norm_num [mhAcceptanceRational]

theorem exercise_49_4_detailed_balance :
    1 * mhAcceptanceRational 1 3 1 1 =
      3 * mhAcceptanceRational 3 1 1 1 := by
  norm_num [mhAcceptanceRational]

theorem exercise_49_5_one_way_proposal_is_rejected
    (wx wy qxy : ℝ) (hqxy : 0 ≤ qxy) :
    min qxy (wy * (0 : ℝ) / wx) = 0 := by
  simp [hqxy]

-- Source Lean fence 3
theorem exercise_49_10_reversible_markov_kernel_is_invariant
    {α : Type*} [MeasurableSpace α] {κ : ProbabilityTheory.Kernel α α}
    [ProbabilityTheory.IsMarkovKernel κ] {π : MeasureTheory.Measure α}
    (hrev : ProbabilityTheory.Kernel.IsReversible κ π) :
    ProbabilityTheory.Kernel.Invariant κ π :=
  hrev.invariant

end Book.Chapters.Chapter49
