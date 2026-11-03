module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 78 — Aggregation and Singular Perturbation of Markov Chains

Extracted from manuscript/chapters/part-21/chapter-78-aggregation-singular-perturbation-markov-chains.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter78

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def aggregateToOneClass (_s : State) : Nat := 0

theorem aggregationErasesTheWithinClassLabel :
    aggregateToOneClass zero = aggregateToOneClass one := by decide

-- Source Lean fence 3
def blockAWeightZero (p q : ℚ) : ℚ := q / (p + q)
def blockAWeightOne (p q : ℚ) : ℚ := p / (p + q)
def blockBWeightZero (r s : ℚ) : ℚ := s / (r + s)
def blockBWeightOne (r s : ℚ) : ℚ := r / (r + s)

def averagedRateAB (p q u v : ℚ) : ℚ :=
  blockAWeightZero p q * u + blockAWeightOne p q * v

def averagedRateBA (r s w z : ℚ) : ℚ :=
  blockBWeightZero r s * w + blockBWeightOne r s * z

theorem blockA_weights_normalized (p q : ℚ) (hp : 0 < p) (hq : 0 < q) :
    blockAWeightZero p q + blockAWeightOne p q = 1 := by
  have hs : p + q ≠ 0 := ne_of_gt (add_pos hp hq)
  unfold blockAWeightZero blockAWeightOne
  field_simp [hs]
  ring

theorem blockB_weights_normalized (r s : ℚ) (hr : 0 < r) (hs : 0 < s) :
    blockBWeightZero r s + blockBWeightOne r s = 1 := by
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold blockBWeightZero blockBWeightOne
  field_simp [hrs]
  ring

theorem residualA_centered (p q u v : ℚ) (hp : 0 < p) (hq : 0 < q) :
    blockAWeightZero p q * (u - averagedRateAB p q u v) +
      blockAWeightOne p q * (v - averagedRateAB p q u v) = 0 := by
  have hs : p + q ≠ 0 := ne_of_gt (add_pos hp hq)
  unfold averagedRateAB blockAWeightZero blockAWeightOne
  field_simp [hs]
  ring

theorem residualB_centered (r s w z : ℚ) (hr : 0 < r) (hs : 0 < s) :
    blockBWeightZero r s * (w - averagedRateBA r s w z) +
      blockBWeightOne r s * (z - averagedRateBA r s w z) = 0 := by
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold averagedRateBA blockBWeightZero blockBWeightOne
  field_simp [hrs]
  ring

theorem averagedRateAB_exact_lumpability (p q u : ℚ) (hp : 0 < p) (hq : 0 < q) :
    averagedRateAB p q u u = u := by
  have hs : p + q ≠ 0 := ne_of_gt (add_pos hp hq)
  unfold averagedRateAB blockAWeightZero blockAWeightOne
  field_simp [hs]
  ring

theorem averagedRateBA_exact_lumpability (r s w : ℚ)
    (hr : 0 < r) (hs : 0 < s) : averagedRateBA r s w w = w := by
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold averagedRateBA blockBWeightZero blockBWeightOne
  field_simp [hrs]
  ring

inductive ReducedBlock where
  | A
  | B
  deriving DecidableEq

def reducedGenerator (p q r s u v w z : ℚ) :
    ReducedBlock → ReducedBlock → ℚ
  | .A, .A => -averagedRateAB p q u v
  | .A, .B => averagedRateAB p q u v
  | .B, .A => averagedRateBA r s w z
  | .B, .B => -averagedRateBA r s w z

theorem reducedGenerator_rowA_sum (p q r s u v w z : ℚ) :
    reducedGenerator p q r s u v w z .A .A +
      reducedGenerator p q r s u v w z .A .B = 0 := by
  simp [reducedGenerator]

theorem reducedGenerator_rowB_sum (p q r s u v w z : ℚ) :
    reducedGenerator p q r s u v w z .B .A +
      reducedGenerator p q r s u v w z .B .B = 0 := by
  simp [reducedGenerator]

end Book.Chapters.Chapter78
