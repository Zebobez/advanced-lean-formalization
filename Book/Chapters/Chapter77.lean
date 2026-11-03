module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 77 — Averaging for Fast–Slow Markov Chains

Extracted from manuscript/chapters/part-21/chapter-77-averaging-fast-slow-markov-chains.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter77

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def fastDrift : State → Int := fun s => if s = zero then -1 else 1

theorem averagedFastDriftIsZero :
    expectationNumerator uniformWeight fastDrift = 0 := by decide

-- Source Lean fence 3
def fastStationaryZero (a b : ℚ) : ℚ := b / (a + b)
def fastStationaryOne (a b : ℚ) : ℚ := a / (a + b)

def averagedFastDrift (a b v₀ v₁ : ℚ) : ℚ :=
  fastStationaryZero a b * v₀ + fastStationaryOne a b * v₁

def fastCorrectorZero (a b v₀ v₁ : ℚ) : ℚ :=
  a * (v₀ - v₁) / (a + b) ^ 2

def fastCorrectorOne (a b v₀ v₁ : ℚ) : ℚ :=
  -b * (v₀ - v₁) / (a + b) ^ 2

def fastGeneratorAtZero (a h₀ h₁ : ℚ) : ℚ := a * (h₁ - h₀)
def fastGeneratorAtOne (b h₀ h₁ : ℚ) : ℚ := b * (h₀ - h₁)

theorem fastStationary_normalized (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    fastStationaryZero a b + fastStationaryOne a b = 1 := by
  have hs : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  unfold fastStationaryZero fastStationaryOne
  field_simp [hs]
  ring

theorem averagedFastDrift_centered (a b v₀ v₁ : ℚ)
    (ha : 0 < a) (hb : 0 < b) :
    fastStationaryZero a b * (v₀ - averagedFastDrift a b v₀ v₁) +
      fastStationaryOne a b * (v₁ - averagedFastDrift a b v₀ v₁) = 0 := by
  have hs : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  unfold averagedFastDrift fastStationaryZero fastStationaryOne
  field_simp [hs]
  ring

theorem fastCorrector_centered (a b v₀ v₁ : ℚ)
    (ha : 0 < a) (hb : 0 < b) :
    fastStationaryZero a b * fastCorrectorZero a b v₀ v₁ +
      fastStationaryOne a b * fastCorrectorOne a b v₀ v₁ = 0 := by
  have hs : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  unfold fastStationaryZero fastStationaryOne fastCorrectorZero fastCorrectorOne
  field_simp [hs]
  ring

theorem fastCorrector_solves_zero (a b v₀ v₁ : ℚ)
    (ha : 0 < a) (hb : 0 < b) :
    fastGeneratorAtZero a (fastCorrectorZero a b v₀ v₁)
        (fastCorrectorOne a b v₀ v₁) =
      -(v₀ - averagedFastDrift a b v₀ v₁) := by
  have hs : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  unfold fastGeneratorAtZero fastCorrectorZero fastCorrectorOne
    averagedFastDrift fastStationaryZero fastStationaryOne
  field_simp [hs]
  ring

theorem fastCorrector_solves_one (a b v₀ v₁ : ℚ)
    (ha : 0 < a) (hb : 0 < b) :
    fastGeneratorAtOne b (fastCorrectorZero a b v₀ v₁)
        (fastCorrectorOne a b v₀ v₁) =
      -(v₁ - averagedFastDrift a b v₀ v₁) := by
  have hs : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  unfold fastGeneratorAtOne fastCorrectorZero fastCorrectorOne
    averagedFastDrift fastStationaryZero fastStationaryOne
  field_simp [hs]
  ring

def fastGammaAtZero (a h₀ h₁ : ℚ) : ℚ := a * (h₁ - h₀) ^ 2
def fastGammaAtOne (b h₀ h₁ : ℚ) : ℚ := b * (h₀ - h₁) ^ 2

def fastEnvironmentalCovariance (a b v₀ v₁ : ℚ) : ℚ :=
  fastStationaryZero a b *
      fastGammaAtZero a (fastCorrectorZero a b v₀ v₁)
        (fastCorrectorOne a b v₀ v₁) +
    fastStationaryOne a b *
      fastGammaAtOne b (fastCorrectorZero a b v₀ v₁)
        (fastCorrectorOne a b v₀ v₁)

theorem fastEnvironmentalCovariance_eq (a b v₀ v₁ : ℚ)
    (ha : 0 < a) (hb : 0 < b) :
    fastEnvironmentalCovariance a b v₀ v₁ =
      2 * a * b * (v₀ - v₁) ^ 2 / (a + b) ^ 3 := by
  have hs : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  unfold fastEnvironmentalCovariance fastStationaryZero fastStationaryOne
    fastGammaAtZero fastGammaAtOne fastCorrectorZero fastCorrectorOne
  field_simp [hs]
  ring

end Book.Chapters.Chapter77
