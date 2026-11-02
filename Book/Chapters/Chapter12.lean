module

public import Mathlib

public section

/-!
# Chapter 12 — Finite Types and Combinatorial Proofs

Extracted from manuscript/chapters/part-02/chapter-12-finite-combinatorics.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 1
namespace Chapter12

example {α : Type _} [DecidableEq α] (a : α) : ({a} : Finset α).card = 1 := by
  simp

-- Source Lean fence 2
example (n : Nat) : Fintype.card (Fin n) = n := by
  simp

-- Source Lean fence 4
example {α : Type _} [DecidableEq α] (s t : Finset α)
    (h : Disjoint s t) : (s ∪ t).card = s.card + t.card := by
  exact Finset.card_union_of_disjoint h

-- Source Lean fence 7
open scoped BigOperators

theorem sum_odd_numbers (n : Nat) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring

-- Source Lean fence 8
example {α β : Type _} [Fintype α] [Fintype β] (e : α ≃ β) :
    Fintype.card α = Fintype.card β := by
  exact Fintype.card_congr e

