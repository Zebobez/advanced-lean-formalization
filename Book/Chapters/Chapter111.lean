module

public import Mathlib

public section

/-!
# Chapter 111 — Dykstra’s Algorithm and Projection onto Intersections

Extracted from manuscript/chapters/part-23/chapter-111-dykstra-projection-algorithm.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter111

-- Source Lean fence 1
structure Point111 where
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  deriving Repr

@[ext] theorem point111_ext (u v : Point111)
    (h1 : u.x1 = v.x1) (h2 : u.x2 = v.x2) (h3 : u.x3 = v.x3) : u = v := by
  cases u
  cases v
  simp_all

def addPoint111 (u v : Point111) : Point111 :=
  ⟨u.x1 + v.x1, u.x2 + v.x2, u.x3 + v.x3⟩

def subPoint111 (u v : Point111) : Point111 :=
  ⟨u.x1 - v.x1, u.x2 - v.x2, u.x3 - v.x3⟩

def zeroPoint111 : Point111 := ⟨0, 0, 0⟩

def affineProject111 (v : Point111) : Point111 :=
  let shift := (v.x1 + v.x2 + v.x3 - 1) / 3
  ⟨v.x1 - shift, v.x2 - shift, v.x3 - shift⟩

def nonnegativeProject111 (v : Point111) : Point111 :=
  ⟨max v.x1 0, max v.x2 0, max v.x3 0⟩

def input111 : Point111 := ⟨2, -1, (1 : ℚ) / 2⟩
def yFirst111 : Point111 := affineProject111 (addPoint111 input111 zeroPoint111)
def pFirst111 : Point111 := subPoint111 (addPoint111 input111 zeroPoint111) yFirst111
def xFirst111 : Point111 := nonnegativeProject111 (addPoint111 yFirst111 zeroPoint111)
def qFirst111 : Point111 := subPoint111 (addPoint111 yFirst111 zeroPoint111) xFirst111

theorem first_affine_projection_value :
    yFirst111 = ⟨(11 : ℚ) / 6, -(7 : ℚ) / 6, (1 : ℚ) / 3⟩ := by
  ext <;> norm_num [yFirst111, affineProject111, addPoint111,
    input111, zeroPoint111]

theorem first_dykstra_corrections :
    pFirst111 = ⟨(1 : ℚ) / 6, (1 : ℚ) / 6, (1 : ℚ) / 6⟩ ∧
    qFirst111 = ⟨0, -(7 : ℚ) / 6, 0⟩ := by
  constructor <;> ext <;> norm_num [pFirst111, qFirst111,
    yFirst111, xFirst111, affineProject111, nonnegativeProject111,
    addPoint111, subPoint111, input111, zeroPoint111]

theorem first_intermediate_projection_value :
    xFirst111 = ⟨(11 : ℚ) / 6, 0, (1 : ℚ) / 3⟩ := by
  ext <;> norm_num [xFirst111, yFirst111, affineProject111,
    nonnegativeProject111, addPoint111, input111, zeroPoint111]

theorem correction_invariant_after_first_cycle :
    subPoint111 input111 xFirst111 = addPoint111 pFirst111 qFirst111 := by
  ext <;> norm_num [input111, xFirst111, pFirst111, qFirst111,
    yFirst111, affineProject111, nonnegativeProject111,
    addPoint111, subPoint111, zeroPoint111]

theorem intermediate_point_is_not_in_affine_set :
    xFirst111.x1 + xFirst111.x2 + xFirst111.x3 = (13 : ℚ) / 6 ∧
    1 < xFirst111.x1 + xFirst111.x2 + xFirst111.x3 := by
  norm_num [xFirst111, yFirst111, affineProject111,
    nonnegativeProject111, addPoint111, input111, zeroPoint111]

def correctedInputSecond111 : Point111 := addPoint111 xFirst111 pFirst111
def ySecond111 : Point111 := affineProject111 correctedInputSecond111

theorem correction_is_used_in_second_projection :
    correctedInputSecond111 = ⟨2, (1 : ℚ) / 6, (1 : ℚ) / 2⟩ := by
  ext <;> norm_num [correctedInputSecond111, xFirst111, pFirst111,
    yFirst111, affineProject111, nonnegativeProject111,
    addPoint111, subPoint111, input111, zeroPoint111]

theorem second_affine_projection_value :
    ySecond111 = ⟨(13 : ℚ) / 9, -(7 : ℚ) / 18, -(1 : ℚ) / 18⟩ := by
  ext <;> norm_num [ySecond111, affineProject111, correctedInputSecond111,
    xFirst111, pFirst111, yFirst111, nonnegativeProject111,
    addPoint111, subPoint111, input111, zeroPoint111]

end Book.Chapters.Chapter111
