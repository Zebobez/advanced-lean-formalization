module

public import Mathlib

public section

/-!
# Chapter 18 — Universe Polymorphism and API Design

Extracted from manuscript/chapters/part-02/chapter-18-universes-and-api-design.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter18

-- Source Lean fence 2
universe u

def idSort {α : Sort u} (x : α) : α := x

#check idSort

-- Source Lean fence 3

structure Box (α : Type u) where
  value : α

def Box.extract {α : Type u} (b : Box α) : α := b.value

-- Source Lean fence 4
universe v

def mapPair {α : Type u} {β : Type v} (f : α → β)
    (pair : α × α) : β × β :=
  (f pair.1, f pair.2)

-- Source Lean fence 5

def keepType {α : Type u} (x : α) : α := x
def keepSort {α : Sort u} (x : α) : α := x

-- Source Lean fence 6

def IsFixed {α : Type u} (f : α → α) : Prop :=
  ∀ x, f x = x

-- Source Lean fence 7

def listOfTypes : List (Type u) := []

-- Source Lean fence 8

structure HasRepresentation (α : Type u) where
  Code : Type v
  encode : α → Code

end Book.Chapters.Chapter18
