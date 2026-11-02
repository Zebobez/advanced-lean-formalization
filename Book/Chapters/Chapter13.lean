module

public import Mathlib

public section

/-!
# Chapter 13 — Homomorphisms, Embeddings, and Isomorphisms

Extracted from manuscript/chapters/part-02/chapter-13-bundled-maps.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 1
namespace Chapter13

example {M N : Type _} [Monoid M] [Monoid N]
    (f : M →* N) (a b : M) : f (a * b) = f a * f b := by
  exact map_mul f a b

-- Source Lean fence 2
example {M N : Type _} [Monoid M] [Monoid N]
    (f : M →* N) (a : M) (n : Nat) : f (a ^ n) = f a ^ n := by
  exact map_pow f a n

-- Source Lean fence 3
def firstProjectionHom {M N : Type _} [Monoid M] [Monoid N] : M × N →* M where
  toFun := Prod.fst
  map_one' := rfl
  map_mul' x y := rfl

-- Source Lean fence 4
example {M N : Type _} [Monoid M] [Monoid N]
    (f : M →* N) (a b : M) : f (a * b) = f a * f b := by
  simp

-- Source Lean fence 5
example {M N : Type _} [Monoid M] [Monoid N]
    (f g : M →* N) (h : ∀ x, f x = g x) : f = g := by
  ext x
  exact h x

-- Source Lean fence 6
example {M N : Type _} [Monoid M] [Monoid N] (f : M →* N)
    (hinj : Function.Injective f) {a b : M} (h : f a = f b) : a = b := by
  exact hinj h

