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

end Book.Chapters.Chapter27
