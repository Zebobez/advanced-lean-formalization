module

public import Mathlib

public section

/-!
# Chapter 4 — Prove Equality by Extensionality

Extracted from manuscript/chapters/part-01/chapter-04-extensionality.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter04

-- Source Lean fence 1
example {α β : Type _} (f g : α → β)
    (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

-- Source Lean fence 3
example {α β γ : Type _} (g : α → β) (f₁ f₂ : β → γ)
    (h : ∀ x, f₁ x = f₂ x) : f₁ ∘ g = f₂ ∘ g := by
  funext x
  exact h (g x)

-- Source Lean fence 4
example {α β : Type _} (f g : α → β) (h : f = g) (x : α) :
    f x = g x := by
  exact congrArg (fun k : α → β => k x) h

-- Source Lean fence 5
example {α β : Type _} (R S : α → β → Prop)
    (h : ∀ a b, R a b ↔ S a b) : R = S := by
  funext a
  funext b
  exact propext (h a b)

-- Source Lean fence 6
example : (fun n : Nat => n + 0) = fun n => n := by
  funext n
  simp

-- Source Lean fence 7
example {α : Type _} (s t : Set α)
    (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x

-- Source Lean fence 8
def boundedBy (n : Nat) : Set Nat := {x | x < n}
def belowSucc (n : Nat) : Set Nat := {x | x < n + 1}

-- Source Lean fence 9
example (n : Nat) : boundedBy n = {x | x < n} := by
  ext x
  rfl

-- Source Lean fence 10
structure Bounds where
  lower : Nat
  upper : Nat

-- Source Lean fence 11
example (a b : Bounds)
    (h₁ : a.lower = b.lower) (h₂ : a.upper = b.upper) : a = b := by
  cases a with
  | mk al au =>
    cases b with
    | mk bl bu =>
      simp_all

-- Source Lean fence 12
example {α β : Type _} (p q : α × β)
    (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q := by
  ext <;> assumption

-- Source Lean fence 14
example {α : Type _} {p : α → Prop}
    (x y : {a // p a}) (h : x.val = y.val) : x = y := by
  apply Subtype.ext
  exact h

-- Source Lean fence 15
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  exact propext h

end Book.Chapters.Chapter04
