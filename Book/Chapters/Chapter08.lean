module

public import Mathlib

public section

/-!
# Chapter 8 — Indexed Families and Dependent Elimination

Extracted from manuscript/chapters/part-01/chapter-08-indexed-families.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 1
namespace Chapter08

inductive Vec (α : Type _) : Nat → Type _ where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (Nat.succ n)

-- Source Lean fence 3
def head {n : Nat} : Vec α (Nat.succ n) → α
  | .cons x _ => x

-- Source Lean fence 4
def tail {n : Nat} : Vec α (Nat.succ n) → Vec α n
  | .cons _ xs => xs

-- Source Lean fence 5
example {n : Nat} (v : Vec α (Nat.succ n)) :
    ∃ x xs, v = Vec.cons x xs := by
  cases v with
  | cons x xs => exact ⟨x, xs, rfl⟩

-- Source Lean fence 6
@[expose] def vappend {m n : Nat} : Vec α m → Vec α n → Vec α (n + m)
  | .nil, ys => ys
  | .cons x xs, ys => Vec.cons x (vappend xs ys)

-- Source Lean fence 7
@[simp] theorem vappend_nil {n : Nat} (ys : Vec α n) :
    vappend Vec.nil ys = ys := by
  simp [vappend]

@[simp] theorem vappend_cons {m n : Nat} (x : α)
    (xs : Vec α m) (ys : Vec α n) :
    vappend (Vec.cons x xs) ys = Vec.cons x (vappend xs ys) := by
  simp [vappend]

-- Source Lean fence 8
def mapVec (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (mapVec f xs)

theorem mapVec_id (v : Vec α n) : mapVec id v = v := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [mapVec, ih]

-- Source Lean fence 9
def castVec {m n : Nat} (h : m = n) (xs : Vec α m) : Vec α n :=
  h ▸ xs

-- Source Lean fence 10
def sumVec : Vec Nat n → Nat
  | .nil => 0
  | .cons x xs => x + sumVec xs

