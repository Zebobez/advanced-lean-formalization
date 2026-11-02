module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 81 — Markovian Arrival Processes and MAP/M/1 Queues

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter81

open Book.Models.FiniteTwoState

def queueLength (s : State) : Nat := if s = zero then 0 else 1
def arrivalStep (q : Nat) : Nat := q + 1
def serviceStep (q : Nat) : Nat := q - 1

theorem arrivalRaisesEmptyQueue : arrivalStep (queueLength zero) = 1 := by decide
theorem serviceEmptiesSingleCustomerQueue : serviceStep (queueLength one) = 0 := by decide

end Book.Chapters.Chapter81
