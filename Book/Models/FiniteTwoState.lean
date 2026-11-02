module

public import Lean

public section

/-!
# Finite two-state stochastic models

This small executable model supports the probability, Markov-chain, and queueing
chapters. Probabilities are represented by integer weights with denominator two,
so the examples focus on exact finite calculations.
-/

namespace Book.Models.FiniteTwoState

abbrev State := Fin 2
abbrev Weight := State → Nat
abbrev Kernel := State → State → Nat
abbrev RateMatrix := State → State → Int

@[expose]
def zero : State := 0
@[expose]
def one : State := 1

@[expose]
def uniformWeight : Weight := fun _ => 1

@[expose]
def totalWeight (w : Weight) : Nat := w zero + w one

@[expose]
def expectationNumerator (w : Weight) (f : State → Int) : Int :=
  Int.ofNat (w zero) * f zero + Int.ofNat (w one) * f one

@[expose]
def identityKernel : Kernel := fun i j => if i = j then 2 else 0

@[expose]
def flipKernel : Kernel := fun i j => if i = j then 0 else 2

@[expose]
def resetKernel : Kernel := fun _ _ => 1

@[expose]
def rowMass (k : Kernel) (i : State) : Nat := k i zero + k i one

@[expose]
def pushedWeight (w : Weight) (k : Kernel) (j : State) : Nat :=
  w zero * k zero j + w one * k one j

@[expose]
def invariantAt (w : Weight) (k : Kernel) (j : State) : Prop :=
  pushedWeight w k j = 2 * w j

@[expose]
def detailedBalanceAt (w : Weight) (k : Kernel) (i j : State) : Prop :=
  w i * k i j = w j * k j i

@[expose]
def composeAt (k l : Kernel) (i j : State) : Nat :=
  (k i zero * l zero j + k i one * l one j) / 2

@[expose]
def twoStateGenerator : RateMatrix := fun i j =>
  if i = zero then (if j = zero then -1 else 1)
  else if j = zero then 2 else -2

@[expose]
def generatorRowSum (q : RateMatrix) (i : State) : Int := q i zero + q i one

@[expose]
def generatorAction (q : RateMatrix) (f : State → Int) (i : State) : Int :=
  q i zero * f zero + q i one * f one

theorem uniformWeight_total : totalWeight uniformWeight = 2 := by decide

theorem identity_zero_row : rowMass identityKernel zero = 2 := by decide
theorem identity_one_row : rowMass identityKernel one = 2 := by decide
theorem flip_zero_row : rowMass flipKernel zero = 2 := by decide
theorem flip_one_row : rowMass flipKernel one = 2 := by decide
theorem reset_zero_row : rowMass resetKernel zero = 2 := by decide
theorem reset_one_row : rowMass resetKernel one = 2 := by decide

theorem uniform_flip_invariant_zero : invariantAt uniformWeight flipKernel zero := by
  unfold invariantAt pushedWeight uniformWeight flipKernel
  decide
theorem uniform_flip_invariant_one : invariantAt uniformWeight flipKernel one := by
  unfold invariantAt pushedWeight uniformWeight flipKernel
  decide
theorem uniform_identity_invariant_zero : invariantAt uniformWeight identityKernel zero := by
  unfold invariantAt pushedWeight uniformWeight identityKernel
  decide
theorem uniform_identity_invariant_one : invariantAt uniformWeight identityKernel one := by
  unfold invariantAt pushedWeight uniformWeight identityKernel
  decide

theorem uniform_flip_detailed_balance : detailedBalanceAt uniformWeight flipKernel zero one := by
  unfold detailedBalanceAt uniformWeight flipKernel
  decide
theorem generator_zero_row : generatorRowSum twoStateGenerator zero = 0 := by decide
theorem generator_one_row : generatorRowSum twoStateGenerator one = 0 := by decide

end Book.Models.FiniteTwoState
