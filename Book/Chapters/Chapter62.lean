module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 62 — Coupling and Continuous-Time Mixing

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter62

open Book.Models.FiniteTwoState

def flipState (s : State) : State := if s = zero then one else zero
def synchronousFlip (p : State × State) : State × State :=
  (flipState p.1, flipState p.2)

theorem diagonalCouplingStaysDiagonal :
    synchronousFlip (zero, zero) = (one, one) := by decide

end Book.Chapters.Chapter62
