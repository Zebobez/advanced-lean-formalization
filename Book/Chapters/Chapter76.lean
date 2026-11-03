module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 76 — Population Scaling and Diffusion Limits

Extracted from manuscript/chapters/part-20/chapter-76-population-scaling-and-diffusion-limits.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter76

-- Source Lean fence 2

open Book.Models.FiniteTwoState

def populationCount : State → Nat := fun s => if s = zero then 0 else 1
def scaledPopulation (s : State) : Nat := 2 * populationCount s

theorem scalingPreservesTheZeroState : scaledPopulation zero = 0 := by decide
theorem scalingOfOneIndividual : scaledPopulation one = 2 := by decide

-- Source Lean fence 3
def channelDrift {Coordinate : Type*}
    (channels : List (ℚ × (Coordinate → ℚ))) (i : Coordinate) : ℚ :=
  channels.foldr (fun channel total => channel.1 * channel.2 i + total) 0

def scaledChannelDrift {Coordinate : Type*}
    (channels : List (ℚ × (Coordinate → ℚ))) (i : Coordinate) (N : ℚ) : ℚ :=
  channels.foldr
    (fun channel total => (N * channel.1) * (channel.2 i / N) + total) 0

def channelCovariance {Coordinate : Type*}
    (channels : List (ℚ × (Coordinate → ℚ))) (i j : Coordinate) : ℚ :=
  channels.foldr
    (fun channel total => channel.1 * channel.2 i * channel.2 j + total) 0

def scaledChannelCovariance {Coordinate : Type*}
    (channels : List (ℚ × (Coordinate → ℚ))) (i j : Coordinate) (N : ℚ) : ℚ :=
  channels.foldr
    (fun channel total =>
      (N * channel.1) * (channel.2 i / N) * (channel.2 j / N) + total) 0

theorem scaledChannelDrift_eq {Coordinate : Type*}
    (channels : List (ℚ × (Coordinate → ℚ))) (i : Coordinate)
    (N : ℚ) (hN : N ≠ 0) :
    scaledChannelDrift channels i N = channelDrift channels i := by
  induction channels with
  | nil => rfl
  | cons channel channels ih =>
      change
        (N * channel.1 * (channel.2 i / N) +
          scaledChannelDrift channels i N) =
        channel.1 * channel.2 i + channelDrift channels i
      rw [ih]
      field_simp [hN]

theorem scaledChannelCovariance_eq {Coordinate : Type*}
    (channels : List (ℚ × (Coordinate → ℚ))) (i j : Coordinate)
    (N : ℚ) (hN : N ≠ 0) :
    scaledChannelCovariance channels i j N =
      channelCovariance channels i j / N := by
  induction channels with
  | nil => simp [scaledChannelCovariance, channelCovariance]
  | cons channel channels ih =>
      change
        (N * channel.1 * (channel.2 i / N) * (channel.2 j / N) +
          scaledChannelCovariance channels i j N) =
        (channel.1 * channel.2 i * channel.2 j +
          channelCovariance channels i j) / N
      rw [ih]
      field_simp [hN]

end Book.Chapters.Chapter76
