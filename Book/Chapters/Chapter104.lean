module

public import Mathlib

public section

/-!
# Chapter 104 — Stochastic Frank–Wolfe and Noisy Linear Oracles

Extracted from manuscript/chapters/part-23/chapter-104-stochastic-frank-wolfe.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter104

-- Source Lean fence 1
def inner104 (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

noncomputable def current104 : ℝ × ℝ := ((1 : ℝ) / 2, (1 : ℝ) / 2)
def vertexOne104 : ℝ × ℝ := (1, 0)
def vertexTwo104 : ℝ × ℝ := (0, 1)
def trueGradient104 : ℝ × ℝ := (0, 1)
def noisyGradient104 : ℝ × ℝ := (1, 0)

def progress104 (gradient point atom : ℝ × ℝ) : ℝ :=
  inner104 gradient (point - atom)

theorem exact_oracle_prefers_first_vertex :
    inner104 trueGradient104 vertexOne104 <
      inner104 trueGradient104 vertexTwo104 := by
  norm_num [inner104, trueGradient104, vertexOne104, vertexTwo104]

theorem noisy_oracle_prefers_second_vertex :
    inner104 noisyGradient104 vertexTwo104 <
      inner104 noisyGradient104 vertexOne104 := by
  norm_num [inner104, noisyGradient104, vertexOne104, vertexTwo104]

theorem exact_gap_over_vertices_is_one_half :
    max (progress104 trueGradient104 current104 vertexOne104)
      (progress104 trueGradient104 current104 vertexTwo104) = (1 : ℝ) / 2 := by
  norm_num [progress104, inner104, trueGradient104, current104,
    vertexOne104, vertexTwo104]

theorem noisy_gap_over_vertices_is_one_half :
    max (progress104 noisyGradient104 current104 vertexOne104)
      (progress104 noisyGradient104 current104 vertexTwo104) = (1 : ℝ) / 2 := by
  norm_num [progress104, inner104, noisyGradient104, current104,
    vertexOne104, vertexTwo104]

theorem true_progress_of_noisy_atom_is_negative_one_half :
    progress104 trueGradient104 current104 vertexTwo104 = -(1 : ℝ) / 2 := by
  norm_num [progress104, inner104, trueGradient104, current104, vertexTwo104]

noncomputable def noisyUpdate104 (γ : ℝ) : ℝ × ℝ :=
  ((1 - γ) / 2, (1 + γ) / 2)

def objective104 (point : ℝ × ℝ) : ℝ := point.2

theorem noisy_update_stays_in_simplex (γ : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) :
    0 ≤ (noisyUpdate104 γ).1 ∧ (noisyUpdate104 γ).1 ≤ 1 ∧
    0 ≤ (noisyUpdate104 γ).2 ∧ (noisyUpdate104 γ).2 ≤ 1 ∧
    (noisyUpdate104 γ).1 + (noisyUpdate104 γ).2 = 1 := by
  simp only [noisyUpdate104]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · ring

theorem noisy_update_increases_true_objective (γ : ℝ) :
    objective104 (noisyUpdate104 γ) = objective104 current104 + γ / 2 := by
  norm_num [objective104, noisyUpdate104, current104]
  ring

theorem positive_noisy_step_moves_uphill (γ : ℝ) (hγ : 0 < γ) :
    objective104 current104 < objective104 (noisyUpdate104 γ) := by
  rw [noisy_update_increases_true_objective]
  nlinarith

end Book.Chapters.Chapter104
