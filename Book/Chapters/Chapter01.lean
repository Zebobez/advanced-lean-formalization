module

public import Mathlib

public section

/-!
# Chapter 1 — Generalize Before You Induct

Extracted from manuscript/chapters/part-01/chapter-01-generalizing-before-induction.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

-- Source Lean fence 1
universe u

namespace Chapter01

def reverseAcc {α : Type u} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => reverseAcc xs (x :: acc)

-- Source Lean fence 7
@[simp] theorem reverseAcc_eq_reverse_append
    {α : Type u} (xs acc : List α) :
    reverseAcc xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      calc
        reverseAcc (x :: xs) acc = reverseAcc xs (x :: acc) := rfl
        _ = xs.reverse ++ (x :: acc) := ih (x :: acc)
        _ = xs.reverse ++ ([x] ++ acc) := rfl
        _ = (xs.reverse ++ [x]) ++ acc := by
          exact (List.append_assoc _ _ _).symm
        _ = (x :: xs).reverse ++ acc := by
          rw [List.reverse_cons]

-- Source Lean fence 8
theorem reverseAcc_eq_reverse_append_revert
    {α : Type u} (xs acc : List α) :
    reverseAcc xs acc = xs.reverse ++ acc := by
  revert acc
  induction xs with
  | nil =>
      intro acc
      rfl
  | cons x xs ih =>
      intro acc
      calc
        reverseAcc (x :: xs) acc = reverseAcc xs (x :: acc) := rfl
        _ = xs.reverse ++ (x :: acc) := ih (x :: acc)
        _ = xs.reverse ++ ([x] ++ acc) := rfl
        _ = (xs.reverse ++ [x]) ++ acc := by
          exact (List.append_assoc _ _ _).symm
        _ = (x :: xs).reverse ++ acc := by
          rw [List.reverse_cons]

-- Source Lean fence 12
@[expose] def pushBackAcc {α : Type u} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => pushBackAcc xs (acc ++ [x])

-- Source Lean fence 13
@[simp] theorem pushBackAcc_eq_append
    {α : Type u} (xs acc : List α) :
    pushBackAcc xs acc = acc ++ xs := by
  induction xs generalizing acc with
  | nil =>
      simp [pushBackAcc]
  | cons x xs ih =>
      calc
        pushBackAcc (x :: xs) acc = pushBackAcc xs (acc ++ [x]) := rfl
        _ = (acc ++ [x]) ++ xs := ih (acc ++ [x])
        _ = acc ++ (x :: xs) := by
          simpa using (List.append_assoc acc [x] xs)
end Chapter01

