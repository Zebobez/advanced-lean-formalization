module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 66 — Graphical Constructions for Finite Particle Systems

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter66

open Book.Models.FiniteTwoState

def eventFlip (s : State) : State := if s = zero then one else zero
def applyTwoEvents (s : State) : State := eventFlip (eventFlip s)

theorem twoIdenticalEventsCancel : applyTwoEvents zero = zero := by decide

end Book.Chapters.Chapter66
