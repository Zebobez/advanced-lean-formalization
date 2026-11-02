module

public import Book.Models.FiniteTwoState

public section

/-!
# Chapter 64 — Product Generators and Local Interactions

Finite-state executable examples for this chapter's central constructions.
These checked calculations support the exposition; they do not claim to prove
its general theorems.
-/

namespace Book.Chapters.Chapter64

open Book.Models.FiniteTwoState

def updateFirst (p : State × State) : State × State :=
  (if p.1 = zero then one else zero, p.2)

theorem localUpdateLeavesSecondCoordinate : (updateFirst (zero, one)).2 = one := by decide

end Book.Chapters.Chapter64
