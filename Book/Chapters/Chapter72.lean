module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 72 — Resolvents and Green Kernels

Extracted from manuscript/chapters/part-18/chapter-72-resolvents-and-green-kernels.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter72

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def truncatedGreenMass : Nat :=
  rowMass identityKernel zero + rowMass flipKernel zero

theorem twoTermGreenCalculation : truncatedGreenMass = 4 := by decide

-- Source Lean fence 3
def resolvent00 (α a b : ℚ) : ℚ := (α + b) / (α * (α + a + b))
def resolvent01 (α a b : ℚ) : ℚ := a / (α * (α + a + b))
def resolvent10 (α a b : ℚ) : ℚ := b / (α * (α + a + b))
def resolvent11 (α a b : ℚ) : ℚ := (α + a) / (α * (α + a + b))

theorem resolvent_denominator_positive (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < α * (α + a + b) := by
  apply mul_pos hα
  positivity

theorem resolvent_left_product_00 (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (α + a) * resolvent00 α a b - a * resolvent10 α a b = 1 := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent00 resolvent10
  field_simp [hα', ne_of_gt hsum]
  ring

theorem resolvent_left_product_01 (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (α + a) * resolvent01 α a b - a * resolvent11 α a b = 0 := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent01 resolvent11
  field_simp [hα', ne_of_gt hsum]
  ring

theorem resolvent_left_product_10 (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    -b * resolvent00 α a b + (α + b) * resolvent10 α a b = 0 := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent00 resolvent10
  field_simp [hα', ne_of_gt hsum]
  ring

theorem resolvent_left_product_11 (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    -b * resolvent01 α a b + (α + b) * resolvent11 α a b = 1 := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent01 resolvent11
  field_simp [hα', ne_of_gt hsum]
  ring

theorem resolvent_row_sum_zero (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    resolvent00 α a b + resolvent01 α a b = 1 / α := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent00 resolvent01
  field_simp [hα', ne_of_gt hsum]
  ring

theorem resolvent_row_sum_one (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    resolvent10 α a b + resolvent11 α a b = 1 / α := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent10 resolvent11
  field_simp [hα', ne_of_gt hsum]
  ring

end Book.Chapters.Chapter72
