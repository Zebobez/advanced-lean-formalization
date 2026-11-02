module

public import Lean

public section

/-!
# Finite optimization model

The optimization chapters use a three-candidate objective and exact discrete
updates. These examples formalize feasibility, improvement, and residual facts
without suggesting that the finite toy problem proves a general convergence
theorem.
-/

namespace Book.Models.FiniteOptimization

abbrev Candidate := Fin 3

@[expose]
def first : Candidate := 0
@[expose]
def middle : Candidate := 1
@[expose]
def last : Candidate := 2

@[expose]
def loss (x : Candidate) : Nat :=
  if x.val = 0 then 4 else if x.val = 1 then 1 else 0

@[expose]
def gradientStep (x : Candidate) : Candidate :=
  if x.val = 0 then middle else last

@[expose]
def projectedStep (x : Candidate) : Candidate :=
  if x.val = 0 then first else last

@[expose]
def objectiveGap (x : Candidate) : Nat := loss x - loss last

@[expose]
def pairMass (left right : Nat) : Nat := left + right

@[expose]
def transferOne (left right : Nat) : Nat × Nat := (left - 1, right + 1)

@[expose]
def residual (x y : Int) : Int := x - y

theorem first_loss : loss first = 4 := by decide
theorem middle_loss : loss middle = 1 := by decide
theorem last_loss : loss last = 0 := by decide
theorem last_beats_first : loss last ≤ loss first := by decide
theorem last_beats_middle : loss last ≤ loss middle := by decide

theorem first_gradient_step_improves : loss (gradientStep first) < loss first := by decide
theorem middle_gradient_step_improves : loss (gradientStep middle) < loss middle := by decide
theorem projected_first_is_feasible :
    projectedStep first = first ∨ projectedStep first = last := by decide
theorem projected_middle_is_feasible :
    projectedStep middle = first ∨ projectedStep middle = last := by decide
theorem projected_last_is_feasible :
    projectedStep last = first ∨ projectedStep last = last := by decide

theorem gap_at_last : objectiveGap last = 0 := by decide
theorem equal_point_residual_zero (x : Int) : residual x x = 0 := by simp [residual]
theorem transfer_example_preserves_mass :
    pairMass (transferOne 1 1).1 (transferOne 1 1).2 = pairMass 1 1 := by decide

end Book.Models.FiniteOptimization
