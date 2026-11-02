module

public import Mathlib

public section

/-!
# Chapter 6 — Recursive Definitions and Equation Lemmas

Extracted from manuscript/chapters/part-01/chapter-06-recursive-definitions.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 1
namespace Chapter06

inductive Tree (α : Type _) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  deriving Repr

-- Source Lean fence 2
@[expose] def mapTree (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .node left right => .node (mapTree f left) (mapTree f right)

-- Source Lean fence 3
example (f : α → β) (a : α) :
    mapTree f (.leaf a) = .leaf (f a) := rfl

example (f : α → β) (l r : Tree α) :
    mapTree f (.node l r) = .node (mapTree f l) (mapTree f r) := rfl

-- Source Lean fence 4
example (f : α → β) (a : α) : mapTree f (.leaf a) = .leaf (f a) := rfl

example (f : α → β) (l r : Tree α) :
    mapTree f (.node l r) = .node (mapTree f l) (mapTree f r) := rfl

-- Source Lean fence 5
@[simp] theorem mapTree_leaf (f : α → β) (a : α) :
    mapTree f (.leaf a) = .leaf (f a) := rfl

@[simp] theorem mapTree_node (f : α → β) (l r : Tree α) :
    mapTree f (.node l r) = .node (mapTree f l) (mapTree f r) := rfl

-- Source Lean fence 6
example (f : α → β) (l r : Tree α) :
    mapTree f (.node l r) = .node (mapTree f l) (mapTree f r) := by
  simp

-- Source Lean fence 7
theorem mapTree_id (t : Tree α) : mapTree id t = t := by
  induction t with
  | leaf a => rfl
  | node l r ihLeft ihRight =>
      simp [mapTree, ihLeft, ihRight]

-- Source Lean fence 9
@[expose] def leafCount : Tree α → Nat
  | .leaf _ => 1
  | .node left right => leafCount left + leafCount right

@[simp] theorem leafCount_leaf (a : α) : leafCount (.leaf a) = 1 := rfl

@[simp] theorem leafCount_node (l r : Tree α) :
    leafCount (.node l r) = leafCount l + leafCount r := rfl

-- Source Lean fence 10
theorem leafCount_map (f : α → β) (t : Tree α) :
    leafCount (mapTree f t) = leafCount t := by
  induction t with
  | leaf a => rfl
  | node l r ihLeft ihRight =>
      simp [ihLeft, ihRight]

-- Source Lean fence 11
def leaves : Tree α → List α
  | .leaf a => [a]
  | .node left right => leaves left ++ leaves right

-- Source Lean fence 12
def leavesAcc : Tree α → List α → List α
  | .leaf a, acc => a :: acc
  | .node left right, acc => leavesAcc left (leavesAcc right acc)

def leavesFast (t : Tree α) : List α := leavesAcc t []

-- Source Lean fence 13
theorem leavesAcc_spec (t : Tree α) (acc : List α) :
    leavesAcc t acc = leaves t ++ acc := by
  induction t generalizing acc with
  | leaf a => rfl
  | node left right ihLeft ihRight =>
      simp [leavesAcc, leaves, ihLeft, ihRight, List.append_assoc]

-- Source Lean fence 14
theorem leavesFast_eq (t : Tree α) : leavesFast t = leaves t := by
  simp [leavesFast, leavesAcc_spec]

-- Source Lean fence 15
variable (P Q : α → Prop) (step : α → α)
variable (step_eq : ∀ x, step x = x)
variable (proofOfQ : ∀ {x}, P x → Q x)

example (x : α) (h : P x) : Q (step x) := by
  rw [step_eq x]
  -- The goal now uses the right-hand side of the equation.
  exact proofOfQ h

-- Source Lean fence 16
variable (stepNat : Nat → Nat) (baseCase : Nat)

theorem step_zero (n : Nat) (h : n = 0)
    (stepNat_zero : stepNat 0 = baseCase) : stepNat n = baseCase := by
  subst n
  exact stepNat_zero

