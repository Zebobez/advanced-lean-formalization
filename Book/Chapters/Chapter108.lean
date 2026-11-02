module

public import Book.Models.FiniteOptimization

public section

/-!
# Chapter 108 — Frank–Wolfe, Fenchel Duality, and Saddle-Point Certificates

A small, executable finite example illustrating a technique from this chapter.
The example checks the stated computation or invariant; it is not a formal
proof of the chapter's general analytic convergence claims.
-/

namespace Book.Chapters.Chapter108

open Book.Models.FiniteOptimization

def primalValue (x : Nat) : Int := Int.ofNat x
def dualValue (y : Nat) : Int := -Int.ofNat y
def fenchelGap (x y : Nat) : Int := primalValue x + dualValue y

theorem matching_primal_dual_values_have_zero_gap (x : Nat) : fenchelGap x x = 0 := by simp [fenchelGap, primalValue, dualValue]; omega

end Book.Chapters.Chapter108
