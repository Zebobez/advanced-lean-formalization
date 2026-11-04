module

public import Mathlib

public section

/-!
# Chapter 103 — Nonconvex Frank–Wolfe and Stationarity Certificates

Extracted from manuscript/chapters/part-23/chapter-103-nonconvex-frank-wolfe.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter103

-- Source Lean fence 1
def nonconvexObjective103 : ℝ → ℝ :=
  (fun x : ℝ => x) - (fun x => 6 * x ^ 2) + (fun x => 8 * x ^ 3)

theorem nonconvexObjective103_deriv_at_zero :
    HasDerivAt nonconvexObjective103 1 0 := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id 0
  have hsquare : HasDerivAt (fun x : ℝ => x ^ 2) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ))
  have hcube : HasDerivAt (fun x : ℝ => x ^ 3) 0 0 := by
    simpa using (hasDerivAt_pow 3 (0 : ℝ))
  have hsix : HasDerivAt (fun x : ℝ => 6 * x ^ 2) 0 0 := by
    simpa using hsquare.const_mul (6 : ℝ)
  have height : HasDerivAt (fun x : ℝ => 8 * x ^ 3) 0 0 := by
    simpa using hcube.const_mul (8 : ℝ)
  change HasDerivAt
    ((fun x : ℝ => x) - (fun x => 6 * x ^ 2) + (fun x => 8 * x ^ 3)) 1 0
  simpa using (hid.sub hsix).add height

theorem nonconvexObjective103_at_zero : nonconvexObjective103 0 = 0 := by
  norm_num [nonconvexObjective103]

theorem boundary_fw_gap_zero : (1 : ℝ) * (0 - 0) = 0 := by norm_num

theorem boundary_variational_condition (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (1 : ℝ) * (y - 0) := by
  rcases hy with ⟨hy0, hy1⟩
  nlinarith

theorem nonconvex_boundary_is_local_minimum (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 4) :
    nonconvexObjective103 0 ≤ nonconvexObjective103 x := by
  have hfactor : nonconvexObjective103 x = x * (1 - 2 * x) * (1 - 4 * x) := by
    simp [nonconvexObjective103]
    ring
  rw [nonconvexObjective103_at_zero, hfactor]
  have h2 : 0 ≤ 1 - 2 * x := by linarith
  have h4 : 0 ≤ 1 - 4 * x := by linarith
  exact mul_nonneg (mul_nonneg hx0 h2) h4

theorem nonconvexObjective103_at_one_third :
    nonconvexObjective103 (1 / 3) = -(1 : ℝ) / 27 := by
  norm_num [nonconvexObjective103]

end Book.Chapters.Chapter103
