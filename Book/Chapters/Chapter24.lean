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

-- Source Lean fence 2
#check fun {α : Type*} (l : Filter α) (P : α → Prop) => ∀ᶠ x in l, P x

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

-- Source Lean fence 9
example {α : Type*} {l : Filter α} {P Q : α → Prop}
    (h₁ : ∀ᶠ x in l, P x) (h₂ : ∀ᶠ x in l, Q x) :
    ∀ᶠ x in l, P x ∧ Q x := by
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  exact ⟨hx₁, hx₂⟩

-- Source Lean fence 12
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} (h : ContinuousAt f x) :
    Tendsto f (𝓝 x) (𝓝 (f x)) := by
  exact h

-- Source Lean fence 13
theorem exercise_24_2_via_library
    {X : Type*} [TopologicalSpace X] {u : Nat → X} {x : X}
    (h : ∀ᶠ n in atTop, u n = x) :
    Tendsto u atTop (𝓝 x) := by
  exact tendsto_nhds_of_eventually_eq h

theorem exercise_24_2_via_neighborhoods
    {X : Type*} [TopologicalSpace X] {u : Nat → X} {x : X}
    (h : ∀ᶠ n in atTop, u n = x) :
    Tendsto u atTop (𝓝 x) := by
  rw [Filter.tendsto_def]
  intro s hs
  have hx : x ∈ s := mem_of_mem_nhds hs
  filter_upwards [h] with n hn
  change u n ∈ s
  rw [hn]
  exact hx

-- Source Lean fence 14
theorem exercise_24_3_eventually_le_trans
    {α β : Type*} {l : Filter α} [Preorder β]
    {f g h : α → β}
    (hfg : ∀ᶠ x in l, f x ≤ g x)
    (hgh : ∀ᶠ x in l, g x ≤ h x) :
    ∀ᶠ x in l, f x ≤ h x := by
  filter_upwards [hfg, hgh] with x hxfg hxgh
  exact le_trans hxfg hxgh

-- Source Lean fence 15
theorem exercise_24_4_right_neighborhood_is_finer (x : ℝ) :
    𝓝[Set.Ioi x] x ≤ 𝓝 x := by
  exact nhdsWithin_le_nhds

theorem exercise_24_5_tendsto_preimage
    {α β : Type*} {f : α → β}
    {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Filter.tendsto_def

-- Source Lean fence 16
theorem exercise_24_6_continuous_map_of_sequence_limit
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} {u : Nat → X}
    (hlim : Tendsto u atTop (𝓝 x)) (hcont : ContinuousAt f x) :
    Tendsto (f ∘ u) atTop (𝓝 (f x)) := by
  have hmap : Tendsto f (𝓝 x) (𝓝 (f x)) := hcont
  exact hmap.comp hlim

-- Source Lean fence 17
theorem exercise_24_7_mem_of_neBot_is_nonempty
    {α : Type*} {l : Filter α} [NeBot l] {s : Set α}
    (hs : s ∈ l) : s.Nonempty :=
  Filter.nonempty_of_mem hs

example : (∅ : Set Nat) ∈ (⊥ : Filter Nat) := by simp

example : ¬ (∅ : Set Nat).Nonempty := by simp

end Book.Chapters.Chapter24
