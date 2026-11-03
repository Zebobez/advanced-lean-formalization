module

public import Mathlib

public section

/-!
# Chapter 56 — Uniformization and Poissonization

Extracted from manuscript/chapters/part-11/chapter-56-uniformization-and-poissonization.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter56

-- Source Lean fence 2
def IsStochastic {S : Type*} [Fintype S] (P : Matrix S S ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧
  (∀ x, ∑ y, P x y = 1)

structure Generator (S : Type*) [Fintype S] where
  rate : Matrix S S ℝ
  offDiag_nonneg : ∀ x y, x ≠ y → 0 ≤ rate x y
  row_sum_zero : ∀ x, ∑ y, rate x y = 0

-- Source Lean fence 3
def twoStateUniformizedKernel (_x : Bool) (y : Bool) : ℚ :=
  if y then 1 / 3 else 2 / 3

def twoStateUniformizedRowMass (x : Bool) : ℚ :=
  twoStateUniformizedKernel x false + twoStateUniformizedKernel x true

def twoStateUniformizedSquare (x y : Bool) : ℚ :=
  twoStateUniformizedKernel x false * twoStateUniformizedKernel false y +
    twoStateUniformizedKernel x true * twoStateUniformizedKernel true y

theorem two_state_uniformized_entries_nonnegative (x y : Bool) :
    0 ≤ twoStateUniformizedKernel x y := by
  cases y <;> norm_num [twoStateUniformizedKernel]

theorem two_state_uniformized_rows_normalized (x : Bool) :
    twoStateUniformizedRowMass x = 1 := by
  norm_num [twoStateUniformizedRowMass, twoStateUniformizedKernel]

theorem two_state_uniformized_idempotent (x y : Bool) :
    twoStateUniformizedSquare x y = twoStateUniformizedKernel x y := by
  cases y <;> norm_num [twoStateUniformizedSquare, twoStateUniformizedKernel]

-- Source Lean fence 4
def twoStateUniformizedPush (μ : Bool → ℚ) (y : Bool) : ℚ :=
  μ false * twoStateUniformizedKernel false y +
    μ true * twoStateUniformizedKernel true y

def twoStateUniformizedStationary (y : Bool) : ℚ :=
  if y then 1 / 3 else 2 / 3

theorem two_state_uniformized_push_of_normalized (μ : Bool → ℚ)
    (hμ : μ false + μ true = 1) (y : Bool) :
    twoStateUniformizedPush μ y = twoStateUniformizedStationary y := by
  cases y <;>
    norm_num [twoStateUniformizedPush, twoStateUniformizedKernel,
      twoStateUniformizedStationary] <;>
    nlinarith [hμ]

theorem two_state_uniformized_stationary_normalized :
    twoStateUniformizedStationary false + twoStateUniformizedStationary true = 1 := by
  norm_num [twoStateUniformizedStationary]

theorem two_state_uniformized_stationary_fixed (y : Bool) :
    twoStateUniformizedPush twoStateUniformizedStationary y =
      twoStateUniformizedStationary y := by
  exact two_state_uniformized_push_of_normalized twoStateUniformizedStationary
    two_state_uniformized_stationary_normalized y

end Book.Chapters.Chapter56
