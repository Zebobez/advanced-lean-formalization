module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 71 — Quasi-Stationary Laws and Doob Transforms

Extracted from manuscript/chapters/part-17/chapter-71-quasi-stationarity-and-doob-transforms.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter71

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def killedKernel : Kernel := fun i j =>
  if i = zero then (if j = zero then 1 else 0) else 0

theorem survivalMassAfterKilling : rowMass killedKernel zero = 1 := by decide

-- Source Lean fence 3
def exampleKilledK (i j : State) : ℚ :=
  if i = zero then (if j = zero then -5 else 2)
  else if j = zero then 2 else -2

def exampleH (i : State) : ℚ := if i = zero then 1 else 2
def exampleQSD (i : State) : ℚ := if i = zero then 1 / 3 else 2 / 3

def killedRowAction (f : State → ℚ) (i : State) : ℚ :=
  exampleKilledK i zero * f zero + exampleKilledK i one * f one

def killedLeftAction (j : State) : ℚ :=
  exampleQSD zero * exampleKilledK zero j +
    exampleQSD one * exampleKilledK one j

theorem rightEigenvector_at_zero :
    killedRowAction exampleH zero = -1 * exampleH zero := by
  norm_num [killedRowAction, exampleKilledK, exampleH, zero, one]

theorem rightEigenvector_at_one :
    killedRowAction exampleH one = -1 * exampleH one := by
  norm_num [killedRowAction, exampleKilledK, exampleH, zero, one]

theorem qsd_normalized : exampleQSD zero + exampleQSD one = 1 := by
  norm_num [exampleQSD, zero, one]

theorem leftEigenvector_at_zero :
    killedLeftAction zero = -1 * exampleQSD zero := by
  norm_num [killedLeftAction, exampleQSD, exampleKilledK, zero, one]

theorem leftEigenvector_at_one :
    killedLeftAction one = -1 * exampleQSD one := by
  norm_num [killedLeftAction, exampleQSD, exampleKilledK, zero, one]

def exampleDoobK (i j : State) : ℚ :=
  exampleKilledK i j * exampleH j / exampleH i +
    if i = j then 1 else 0

def doobRowSum (i : State) : ℚ :=
  exampleDoobK i zero + exampleDoobK i one

theorem doob_transform_row_zero : doobRowSum zero = 0 := by
  norm_num [doobRowSum, exampleDoobK, exampleKilledK, exampleH, zero, one]

theorem doob_transform_row_one : doobRowSum one = 0 := by
  norm_num [doobRowSum, exampleDoobK, exampleKilledK, exampleH, zero, one]

def exampleDoobStationary (i : State) : ℚ := if i = zero then 1 / 5 else 4 / 5

def doobLeftAction (j : State) : ℚ :=
  exampleDoobStationary zero * exampleDoobK zero j +
    exampleDoobStationary one * exampleDoobK one j

theorem doob_law_normalized :
    exampleDoobStationary zero + exampleDoobStationary one = 1 := by
  norm_num [exampleDoobStationary, zero, one]

theorem doob_law_stationary_at_zero : doobLeftAction zero = 0 := by
  norm_num [doobLeftAction, exampleDoobStationary, exampleDoobK,
    exampleKilledK, exampleH, zero, one]

theorem doob_law_stationary_at_one : doobLeftAction one = 0 := by
  norm_num [doobLeftAction, exampleDoobStationary, exampleDoobK,
    exampleKilledK, exampleH, zero, one]

theorem doob_law_is_left_right_product (i : State) :
    exampleDoobStationary i =
      (exampleQSD i * exampleH i) /
        (exampleQSD zero * exampleH zero + exampleQSD one * exampleH one) := by
  fin_cases i <;>
    norm_num [exampleDoobStationary, exampleQSD, exampleH, zero, one]

end Book.Chapters.Chapter71
