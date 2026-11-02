module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 67 — Exclusion, Conservation, and Duality

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter67

open Book.Models.FiniteTwoState

def exchangeOccupancies (a b : Nat) : Nat × Nat := (b, a)
def particleCount (p : Nat × Nat) : Nat := p.1 + p.2

theorem exclusionMoveConservesParticles :
    particleCount (exchangeOccupancies 1 0) = particleCount (1, 0) := by decide

end Book.Chapters.Chapter67
