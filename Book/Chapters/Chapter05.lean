module

public import Mathlib

public section

/-!
# Chapter 5 — Subtypes, Invariants, and Equivalences

Extracted from manuscript/chapters/part-01/chapter-05-subtypes-and-equivalences.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 3
namespace Chapter05

abbrev PositiveNat := {n : Nat // 0 < n}

-- Source Lean fence 5
def succPositive (n : PositiveNat) : PositiveNat :=
  ⟨n.val + 1, Nat.succ_pos n.val⟩

-- Source Lean fence 6
def mapSubtype {α β : Type _} {p : α → Prop} {q : β → Prop}
    (f : α → β) (hf : ∀ x, p x → q (f x)) :
    {x // p x} → {y // q y} :=
  fun x => ⟨f x.val, hf x.val x.property⟩

-- Source Lean fence 7
example {α β : Type _} {p : α → Prop} {q : β → Prop}
    (f : α → β) (hf : ∀ x, p x → q (f x)) (x : {a // p a}) :
    (mapSubtype f hf x).val = f x.val := rfl

-- Source Lean fence 8
def lastFin (n : Nat) : Fin (n + 1) :=
  ⟨n, by omega⟩

example (n : Nat) : (lastFin n).val = n := rfl

-- Source Lean fence 9
example (a b : PositiveNat) (h : a.val = b.val) : a = b := by
  apply Subtype.ext
  exact h

-- Source Lean fence 10
example (a b : PositiveNat) (h : a = b) : a.val = b.val := by
  exact congrArg Subtype.val h

-- Source Lean fence 11
def positiveNatEquiv : PositiveNat ≃ Nat where
  toFun n := n.val - 1
  invFun n := ⟨n + 1, Nat.succ_pos n⟩
  left_inv n := by
    apply Subtype.ext
    exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr n.property)
  right_inv n := by
    exact Nat.add_sub_cancel_right n 1

-- Source Lean fence 14
example (n : PositiveNat) :
    positiveNatEquiv.symm (positiveNatEquiv n) = n := by
  simp

example (n : Nat) :
    positiveNatEquiv (positiveNatEquiv.symm n) = n := by
  simp

end Chapter05

