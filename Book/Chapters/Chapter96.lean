module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 96 — Control Variates and Finite-Sum Variance Reduction

Extracted from manuscript/chapters/part-23/chapter-96-control-variates-and-finite-sum-variance-reduction.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter96

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def rawGradientSample : State → Int := fun s => if s = zero then 2 else 4
def baselineGradientSample : State → Int := fun s => if s = zero then 1 else 3
def snapshotGradient : Int := 2
def correctedSample (s : State) : Int :=
  rawGradientSample s - baselineGradientSample s + snapshotGradient

theorem corrected_sample_is_constant : ∀ s, correctedSample s = 3 := by decide

theorem corrected_sample_preserves_mean :
    expectationNumerator uniformWeight correctedSample =
      expectationNumerator uniformWeight rawGradientSample := by decide

theorem raw_gradient_variance_numerator :
    expectationNumerator uniformWeight (fun s => (rawGradientSample s - 3) ^ 2) = 2 := by decide

theorem corrected_sample_variance_numerator :
    expectationNumerator uniformWeight (fun s => (correctedSample s - 3) ^ 2) = 0 := by decide

end Book.Chapters.Chapter96
