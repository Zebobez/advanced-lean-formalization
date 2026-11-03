module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 64 — Product Generators and Local Interactions

Extracted from manuscript/chapters/part-14/chapter-64-product-generators-and-local-interactions.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter64

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def updateFirst (p : State × State) : State × State :=
  (if p.1 = zero then one else zero, p.2)

theorem localUpdateLeavesSecondCoordinate : (updateFirst (zero, one)).2 = one := by decide

-- Source Lean fence 3

open Book.Models.FiniteTwoState

def updateSecond (p : State × State) : State × State :=
  (p.1, if p.2 = zero then one else zero)

def firstCoordinateGeneratorQ (r : ℚ) (f : State × State → ℚ)
    (p : State × State) : ℚ :=
  r * (f (updateFirst p) - f p)

def secondCoordinateGeneratorQ (s : ℚ) (f : State × State → ℚ)
    (p : State × State) : ℚ :=
  s * (f (updateSecond p) - f p)

theorem different_coordinate_updates_commute (p : State × State) :
    updateFirst (updateSecond p) = updateSecond (updateFirst p) := by
  cases p with
  | mk x y => rfl

theorem independent_coordinate_generators_commute (r s : ℚ)
    (f : State × State → ℚ) (p : State × State) :
    firstCoordinateGeneratorQ r (secondCoordinateGeneratorQ s f) p =
      secondCoordinateGeneratorQ s (firstCoordinateGeneratorQ r f) p := by
  simp only [firstCoordinateGeneratorQ, secondCoordinateGeneratorQ]
  rw [← different_coordinate_updates_commute p]
  ring

def interactingFirstGeneratorQ (f : State × State → ℚ)
    (p : State × State) : ℚ :=
  (if p.2 = zero then 1 else 2) * (f (updateFirst p) - f p)

def firstCoordinateIndicatorQ (p : State × State) : ℚ :=
  if p.1 = zero then 1 else 0

theorem local_interaction_breaks_generator_commutation :
    interactingFirstGeneratorQ
        (secondCoordinateGeneratorQ 1 firstCoordinateIndicatorQ) (zero, zero) ≠
      secondCoordinateGeneratorQ 1
        (interactingFirstGeneratorQ firstCoordinateIndicatorQ) (zero, zero) := by
  norm_num [interactingFirstGeneratorQ, secondCoordinateGeneratorQ,
    firstCoordinateIndicatorQ, updateFirst, updateSecond, zero, one]

end Book.Chapters.Chapter64
