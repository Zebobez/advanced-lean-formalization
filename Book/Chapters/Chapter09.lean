module

public import Mathlib

public section

/-!
# Chapter 9 — Quotients and Equivalence Relations

Extracted from manuscript/chapters/part-01/chapter-09-quotients.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 1
namespace Chapter09

def sameParity (a b : Nat) : Prop := a % 2 = b % 2

-- Source Lean fence 2
def paritySetoid : Setoid Nat where
  r := sameParity
  iseqv := {
    refl := by intro a; rfl
    symm := by intro a b h; exact h.symm
    trans := by intro a b c h₁ h₂; exact h₁.trans h₂
  }

abbrev ParityClass := Quotient paritySetoid

-- Source Lean fence 3
theorem parityClass_eq_of_sameParity {a b : Nat} (h : sameParity a b) :
    Quotient.mk paritySetoid a = Quotient.mk paritySetoid b := by
  exact Quotient.sound h

-- Source Lean fence 4
theorem parityClass_eq_iff {a b : Nat} :
    Quotient.mk paritySetoid a = Quotient.mk paritySetoid b ↔ sameParity a b := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

-- Source Lean fence 6
def parityCode (n : Nat) : Fin 2 :=
  ⟨n % 2, Nat.mod_lt _ (by decide)⟩

-- Source Lean fence 7
def parityOfClass : ParityClass → Fin 2 :=
  Quotient.lift parityCode (by
    intro a b h
    apply Fin.ext
    exact h)

-- Source Lean fence 8
@[simp] theorem parityOfClass_mk (n : Nat) :
    parityOfClass (Quotient.mk paritySetoid n) = parityCode n := by
  simp [parityOfClass]

-- Source Lean fence 10
def descend {α β : Type _} (s : Setoid α) (f : α → β)
    (hf : ∀ a b, s.r a b → f a = f b) : Quotient s → β :=
  Quotient.lift f hf

-- Source Lean fence 11
theorem parityClass_has_small_representative (q : ParityClass) :
    ∃ n : Nat, Quotient.mk paritySetoid n = q ∧ n % 2 < 2 := by
  refine Quotient.inductionOn q ?_
  intro n
  refine ⟨n, rfl, ?_⟩
  omega

