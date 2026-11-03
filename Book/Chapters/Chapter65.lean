module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 65 — Graph Laplacians and Effective Resistance

Extracted from manuscript/chapters/part-14/chapter-65-graph-laplacians-and-effective-resistance.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter65

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def neighbor (s : State) : State := if s = zero then one else zero
def contrastPotential : State → Int := fun s => if s = zero then 1 else -1
def graphLaplacian (s : State) : Int := contrastPotential s - contrastPotential (neighbor s)

theorem laplacianAtZero : graphLaplacian zero = 2 := by decide
theorem laplacianAtOne : graphLaplacian one = -2 := by decide

-- Source Lean fence 3

def pathLaplacianQ (c₀ c₁ : ℚ) (f : Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  if i = 0 then c₀ * (f 0 - f 1)
  else if i = 1 then
    c₀ * (f 1 - f 0) + c₁ * (f 1 - f 2)
  else c₁ * (f 2 - f 1)

def pathEnergyQ (c₀ c₁ : ℚ) (f : Fin 3 → ℚ) : ℚ :=
  c₀ * (f 0 - f 1) ^ 2 + c₁ * (f 1 - f 2) ^ 2

def pathLaplacianPairingQ (c₀ c₁ : ℚ) (f : Fin 3 → ℚ) : ℚ :=
  f 0 * pathLaplacianQ c₀ c₁ f 0 +
    f 1 * pathLaplacianQ c₀ c₁ f 1 +
    f 2 * pathLaplacianQ c₀ c₁ f 2

def pathVoltageQ (c₀ c₁ : ℚ) (i : Fin 3) : ℚ :=
  if i = 0 then 1 else if i = 1 then c₀ / (c₀ + c₁) else 0

theorem path_energy_eq_laplacian_pairing (c₀ c₁ : ℚ) (f : Fin 3 → ℚ) :
    pathEnergyQ c₀ c₁ f = pathLaplacianPairingQ c₀ c₁ f := by
  simp [pathEnergyQ, pathLaplacianPairingQ, pathLaplacianQ]
  ring

theorem path_voltage_boundary_values (c₀ c₁ : ℚ) :
    pathVoltageQ c₀ c₁ 0 = 1 ∧ pathVoltageQ c₀ c₁ 2 = 0 := by
  simp [pathVoltageQ]

theorem path_voltage_is_harmonic (c₀ c₁ : ℚ)
    (h : c₀ + c₁ ≠ 0) :
    pathLaplacianQ c₀ c₁ (pathVoltageQ c₀ c₁) 1 = 0 := by
  simp [pathLaplacianQ, pathVoltageQ]
  field_simp [h]
  ring

theorem path_voltage_energy (c₀ c₁ : ℚ) (h : c₀ + c₁ ≠ 0) :
    pathEnergyQ c₀ c₁ (pathVoltageQ c₀ c₁) = c₀ * c₁ / (c₀ + c₁) := by
  simp [pathEnergyQ, pathVoltageQ]
  field_simp [h]
  ring

theorem path_energy_completion_of_square (c₀ c₁ : ℚ)
    (h : c₀ + c₁ ≠ 0) (f : Fin 3 → ℚ)
    (h₀ : f 0 = 1) (h₂ : f 2 = 0) :
    pathEnergyQ c₀ c₁ f =
      pathEnergyQ c₀ c₁ (pathVoltageQ c₀ c₁) +
        (c₀ + c₁) * (f 1 - c₀ / (c₀ + c₁)) ^ 2 := by
  simp only [pathEnergyQ]
  rw [h₀, h₂]
  simp [pathVoltageQ]
  field_simp [h]
  ring

theorem path_voltage_minimizes_energy (c₀ c₁ : ℚ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (f : Fin 3 → ℚ)
    (h : c₀ + c₁ ≠ 0) (h₀ : f 0 = 1) (h₂ : f 2 = 0) :
    pathEnergyQ c₀ c₁ (pathVoltageQ c₀ c₁) ≤ pathEnergyQ c₀ c₁ f := by
  rw [path_energy_completion_of_square c₀ c₁ h f h₀ h₂]
  have hsum : 0 ≤ c₀ + c₁ := by linarith
  have hsq : 0 ≤ (f 1 - c₀ / (c₀ + c₁)) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hsum hsq]

theorem path_effective_conductance_times_resistance (c₀ c₁ : ℚ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    (c₀ * c₁ / (c₀ + c₁)) * ((c₀ + c₁) / (c₀ * c₁)) = 1 := by
  have hsum : c₀ + c₁ ≠ 0 := ne_of_gt (by linarith)
  have hprod : c₀ * c₁ ≠ 0 := mul_ne_zero (ne_of_gt hc₀) (ne_of_gt hc₁)
  field_simp [hsum, hprod]

theorem path_effective_resistance_is_series_sum (c₀ c₁ : ℚ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    (c₀ + c₁) / (c₀ * c₁) = 1 / c₀ + 1 / c₁ := by
  have hprod : c₀ * c₁ ≠ 0 := mul_ne_zero (ne_of_gt hc₀) (ne_of_gt hc₁)
  field_simp [ne_of_gt hc₀, ne_of_gt hc₁, hprod]
  ring

end Book.Chapters.Chapter65
