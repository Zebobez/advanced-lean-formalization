module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 70 — Tilted Generators and Large Deviations

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter70

open Book.Models.FiniteTwoState

def potential (s : State) : Int := if s = zero then 0 else 1
def tiltedRowAtOne : Int :=
  twoStateGenerator one zero + (twoStateGenerator one one + potential one)

theorem tiltAddsTheStatePotential : tiltedRowAtOne = 1 := by decide

end Book.Chapters.Chapter70
