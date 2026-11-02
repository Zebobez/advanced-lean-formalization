module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 60 — Spectral Gaps and Continuous-Time Mixing

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter60

open Book.Models.FiniteTwoState

def contrast : State → Int := fun s => if s = zero then 1 else -1
def flipActionAtZero : Int :=
  Int.ofNat (flipKernel zero zero) * contrast zero +
  Int.ofNat (flipKernel zero one) * contrast one

theorem flipNegatesTheContrast : flipActionAtZero = -2 := by decide

end Book.Chapters.Chapter60
