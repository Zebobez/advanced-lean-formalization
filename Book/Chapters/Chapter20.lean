module

public import Lean
public import Mathlib

public section

/-!
# Chapter 20 — Authoring Tactics with Macros and Elaborators

Extracted from manuscript/chapters/part-03/chapter-20-authoring-tactics.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter20

-- Source Lean fence 2

syntax "assumption_or_rfl" : tactic

macro_rules
  | `(tactic| assumption_or_rfl) => `(tactic| first | assumption | rfl)

example (p : Prop) (hp : p) : p := by
  assumption_or_rfl

example (n : Nat) : n = n := by
  assumption_or_rfl

-- Source Lean fence 3
syntax "try_then_assumption " tacticSeq : tactic

macro_rules
  | `(tactic| try_then_assumption $firstTac:tacticSeq) =>
      `(tactic| first | $firstTac | assumption)

-- Source Lean fence 5

open Lean Elab Tactic

elab "report_target" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  logInfo m!"target: {target}"

-- Source Lean fence 6
example (n : Nat) : n = n := by
  report_target
  rfl

end Book.Chapters.Chapter20
