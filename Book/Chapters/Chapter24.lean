module

public import Mathlib

public section

/-!
# Chapter 24 — Filters and Convergence

Extracted from manuscript/chapters/part-04/chapter-24-filters-and-convergence.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter24

-- Source Lean fence 1
open Filter Topology

-- Source Lean fence 4
example {α β : Type*} {f : α → β}
    {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ := by
  exact Filter.tendsto_def

-- Source Lean fence 6
example {u : Nat → Real} {x : Real}
    (h : ∀ᶠ n in atTop, u n = x) :
    Tendsto u atTop (𝓝 x) := by
  exact tendsto_nhds_of_eventually_eq h

-- Source Lean fence 7
example {X : Type*} [TopologicalSpace X] (x : X) :
    Tendsto (fun _ : Nat => x) atTop (𝓝 x) := by
  exact tendsto_const_nhds

-- Source Lean fence 8
example {α : Type*} {l : Filter α} {P Q : α → Prop}
    (hP : ∀ᶠ x in l, P x)
    (hPQ : ∀ x, P x → Q x) :
    ∀ᶠ x in l, Q x := by
  filter_upwards [hP] with x hx
  exact hPQ x hx

-- Source Lean fence 12
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} (h : ContinuousAt f x) :
    Tendsto f (𝓝 x) (𝓝 (f x)) := by
  exact h

end Book.Chapters.Chapter24
