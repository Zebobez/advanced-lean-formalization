module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 70 — Tilted Generators and Large Deviations

Extracted from manuscript/chapters/part-17/chapter-70-tilted-generators-and-large-deviations.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter70

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def potential (s : State) : Int := if s = zero then 0 else 1
def tiltedRowAtOne : Int :=
  twoStateGenerator one zero + (twoStateGenerator one one + potential one)

theorem tiltAddsTheStatePotential : tiltedRowAtOne = 1 := by decide

-- Source Lean fence 3
def occupationTiltedEntry (θ : Int) (i j : State) : Int :=
  twoStateGenerator i j + if i = j then θ * potential i else 0

def occupationTiltedRowSum (θ : Int) (i : State) : Int :=
  occupationTiltedEntry θ i zero + occupationTiltedEntry θ i one

theorem occupationTiltedRowSum_eq (θ : Int) (i : State) :
    occupationTiltedRowSum θ i = θ * potential i := by
  fin_cases i <;>
    simp [occupationTiltedRowSum, occupationTiltedEntry, potential,
      twoStateGenerator, zero, one]

end Book.Chapters.Chapter70
