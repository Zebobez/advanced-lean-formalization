module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 66 — Graphical Constructions for Finite Particle Systems

Extracted from manuscript/chapters/part-15/chapter-66-graphical-constructions-for-particle-systems.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter66

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def eventFlip (s : State) : State := if s = zero then one else zero
def applyTwoEvents (s : State) : State := eventFlip (eventFlip s)

theorem twoIdenticalEventsCancel : applyTwoEvents zero = zero := by decide

-- Source Lean fence 3
def applyEvents {Ω Event : Type} (update : Event → Ω → Ω)
    (events : List Event) (initial : Ω) : Ω :=
  events.foldl (fun state event => update event state) initial

theorem applyEvents_cons {Ω Event : Type} (update : Event → Ω → Ω)
    (event : Event) (events : List Event) (initial : Ω) :
    applyEvents update (event :: events) initial =
      applyEvents update events (update event initial) := by
  rfl

theorem applyEvents_append {Ω Event : Type} (update : Event → Ω → Ω)
    (first second : List Event) (initial : Ω) :
    applyEvents update (first ++ second) initial =
      applyEvents update second (applyEvents update first initial) := by
  induction first generalizing initial with
  | nil => rfl
  | cons event first ih =>
      rw [List.cons_append, applyEvents_cons, ih, applyEvents_cons]

theorem applyEvents_monotone {Ω Event : Type} [Preorder Ω]
    (update : Event → Ω → Ω)
    (preservesOrder : ∀ event, Monotone (update event))
    (events : List Event) : Monotone (applyEvents update events) := by
  induction events with
  | nil =>
      intro x y hxy
      exact hxy
  | cons event events ih =>
      intro x y hxy
      rw [applyEvents_cons, applyEvents_cons]
      exact ih (preservesOrder event hxy)

def applySharedMarks {Ω Event : Type} (update : Event → Ω → Ω)
    (events : List Event) (initial : Ω × Ω) : Ω × Ω :=
  events.foldl
    (fun pair event => (update event pair.1, update event pair.2)) initial

theorem applySharedMarks_fst {Ω Event : Type}
    (update : Event → Ω → Ω) (events : List Event) (x y : Ω) :
    (applySharedMarks update events (x, y)).1 =
      applyEvents update events x := by
  induction events generalizing x y with
  | nil => rfl
  | cons event events ih =>
      change
        (applySharedMarks update events
          (update event x, update event y)).1 =
        applyEvents update events (update event x)
      exact ih (update event x) (update event y)

theorem applySharedMarks_snd {Ω Event : Type}
    (update : Event → Ω → Ω) (events : List Event) (x y : Ω) :
    (applySharedMarks update events (x, y)).2 =
      applyEvents update events y := by
  induction events generalizing x y with
  | nil => rfl
  | cons event events ih =>
      change
        (applySharedMarks update events
          (update event x, update event y)).2 =
        applyEvents update events (update event y)
      exact ih (update event x) (update event y)

theorem applySharedMarks_preservesOrder {Ω Event : Type} [Preorder Ω]
    (update : Event → Ω → Ω)
    (preservesOrder : ∀ event, Monotone (update event))
    (events : List Event) (x y : Ω × Ω)
    (h₁ : x.1 ≤ y.1) (h₂ : x.2 ≤ y.2) :
    (applySharedMarks update events x).1 ≤
        (applySharedMarks update events y).1 ∧
      (applySharedMarks update events x).2 ≤
        (applySharedMarks update events y).2 := by
  rw [applySharedMarks_fst, applySharedMarks_fst,
    applySharedMarks_snd, applySharedMarks_snd]
  exact ⟨applyEvents_monotone update preservesOrder events h₁,
    applyEvents_monotone update preservesOrder events h₂⟩

end Book.Chapters.Chapter66
