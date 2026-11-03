module

public import Mathlib

public section

/-!
# Chapter 83 — M/G/1-Type Chains and Batch Arrivals

Extracted from manuscript/chapters/part-22/chapter-83-mg1-type-chains-and-batch-arrivals.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter83

-- Source Lean fence 1
abbrev BatchMatrix := Matrix (Fin 2) (Fin 2) ℚ

def batchPhaseKernel : BatchMatrix := !![4 / 5, 1 / 5; 1 / 10, 9 / 10]
def batchPhaseStationary (i : Fin 2) : ℚ := if i = 0 then 1 / 3 else 2 / 3
def batchZeroBlock : BatchMatrix := !![18 / 25, 9 / 50; 3 / 50, 27 / 50]
def batchThreeBlock : BatchMatrix := !![2 / 25, 1 / 50; 1 / 25, 9 / 25]

def batchRowMultiply (p : Fin 2 → ℚ) (A : BatchMatrix) (j : Fin 2) : ℚ :=
  ∑ i : Fin 2, p i * A i j

def conditionalBatchMean (i : Fin 2) : ℚ :=
  3 * ∑ j : Fin 2, batchThreeBlock i j

def stationaryBatchMean : ℚ :=
  ∑ i : Fin 2, batchPhaseStationary i * conditionalBatchMean i

def positiveLevelNext (level batch : Nat) : Nat := level - 1 + batch

theorem batchPhaseStationary_normalized :
    ∑ i : Fin 2, batchPhaseStationary i = 1 := by
  norm_num [batchPhaseStationary]

theorem batchPhaseStationary_invariant :
    ∀ j : Fin 2,
      batchRowMultiply batchPhaseStationary batchPhaseKernel j =
        batchPhaseStationary j := by
  intro j
  fin_cases j <;>
    norm_num [batchRowMultiply, batchPhaseStationary, batchPhaseKernel]

theorem batchPhaseKernel_rows_stochastic (i : Fin 2) :
    ∑ j : Fin 2, batchPhaseKernel i j = 1 := by
  fin_cases i <;> norm_num [batchPhaseKernel]

theorem batch_blocks_decompose_phase_kernel :
    batchZeroBlock + batchThreeBlock = batchPhaseKernel := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [batchZeroBlock, batchThreeBlock, batchPhaseKernel, Matrix.add_apply]

theorem batch_blocks_row_mass_one (i : Fin 2) :
    ∑ j : Fin 2, (batchZeroBlock + batchThreeBlock) i j = 1 := by
  rw [batch_blocks_decompose_phase_kernel]
  exact batchPhaseKernel_rows_stochastic i

theorem batch_blocks_nonnegative :
    (∀ i j : Fin 2, 0 ≤ batchZeroBlock i j) ∧
      (∀ i j : Fin 2, 0 ≤ batchThreeBlock i j) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [batchZeroBlock, batchThreeBlock]

theorem conditional_batch_means :
    (conditionalBatchMean 0 = 3 / 10) ∧
      (conditionalBatchMean 1 = 6 / 5) := by
  norm_num [conditionalBatchMean, batchThreeBlock]

theorem batch_stationary_mean_is_nine_tenths : stationaryBatchMean = 9 / 10 := by
  norm_num [stationaryBatchMean, conditionalBatchMean, batchPhaseStationary,
    batchThreeBlock]

theorem batch_drift_is_negative : stationaryBatchMean < 1 := by
  rw [batch_stationary_mean_is_nine_tenths]
  norm_num

theorem positiveLevel_zero_batch_moves_down (level : Nat) :
    positiveLevelNext level 0 = level - 1 := by
  simp [positiveLevelNext]

theorem positiveLevel_three_batch_skips_up_two (level : Nat) (hlevel : 0 < level) :
    positiveLevelNext level 3 = level + 2 := by
  simp [positiveLevelNext]
  omega

theorem emptyLevel_three_batch_reaches_three : positiveLevelNext 0 3 = 3 := by
  norm_num [positiveLevelNext]

end Book.Chapters.Chapter83
