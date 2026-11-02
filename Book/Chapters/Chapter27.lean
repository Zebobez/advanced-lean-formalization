module

public import Mathlib

public section

/-!
# Chapter 27 — Compactness and Completeness

Extracted from manuscript/chapters/part-04/chapter-27-compactness-and-completeness.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter27

-- Source Lean fence 2
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsCompact s) {f : X → Y}
    (hf : Continuous f) : IsCompact (f '' s) := by
  exact hs.image hf

-- Source Lean fence 3
example {s : Set ℝ} (hc : IsClosed s)
    (hb : Bornology.IsBounded s) : IsCompact s := by
  exact Metric.isCompact_of_isClosed_isBounded hc hb

-- Source Lean fence 5
open Filter Topology

-- Source Lean fence 6
theorem exercise_27_3_closed_subset_compact
    {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsCompact s) (ht : IsClosed t) (hts : t ⊆ s) :
    IsCompact t := by
  exact hs.of_isClosed_subset ht hts

-- Source Lean fence 7
theorem exercise_27_6_cauchy_sequence_converges
    {X : Type*} [UniformSpace X] [CompleteSpace X]
    (u : Nat → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) := by
  exact cauchySeq_tendsto_of_complete hu

-- Source Lean fence 8
theorem exercise_27_7_closed_subtype_complete
    {X : Type*} [UniformSpace X] [CompleteSpace X]
    {s : Set X} (hs : IsClosed s) : CompleteSpace s := by
  exact hs.isComplete.completeSpace_coe

end Book.Chapters.Chapter27
