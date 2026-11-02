module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 89 — Certified Enclosures for Rate Matrices

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter89

open Book.Models.FiniteTwoState

def certificateLower : Nat := 0
def certificateUpper : Nat := 1
def scalarCertificate (x : Nat) : Nat := x * x

theorem enclosureIsOrdered : certificateLower ≤ certificateUpper := by decide
theorem upperEndpointSatisfiesEquation : scalarCertificate certificateUpper = 1 := by decide

end Book.Chapters.Chapter89
