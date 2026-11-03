module

public import Book.Models.FiniteTwoState
public import Mathlib

public section

/-!
# Chapter 67 — Exclusion, Conservation, and Duality

Extracted from manuscript/chapters/part-15/chapter-67-exclusion-conservation-and-duality.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter67

-- Source Lean fence 1

open Book.Models.FiniteTwoState

def exchangeOccupancies (a b : Nat) : Nat × Nat := (b, a)
def particleCount (p : Nat × Nat) : Nat := p.1 + p.2

theorem exclusionMoveConservesParticles :
    particleCount (exchangeOccupancies 1 0) = particleCount (1, 0) := by decide

-- Source Lean fence 2
inductive ExclusionSite where
  | left
  | right
  deriving DecidableEq

abbrev ExclusionConfig := ExclusionSite → Bool

def swapSite : ExclusionSite → ExclusionSite
  | .left => .right
  | .right => .left

def swapConfig (η : ExclusionConfig) : ExclusionConfig :=
  fun site => η (swapSite site)

def siteParticleCount (η : ExclusionConfig) : Int :=
  (if η .left then 1 else 0) + (if η .right then 1 else 0)

theorem swapConfig_involutive (η : ExclusionConfig) :
    swapConfig (swapConfig η) = η := by
  funext site
  cases site <;> rfl

theorem swapConfig_conserves_particles (η : ExclusionConfig) :
    siteParticleCount (swapConfig η) = siteParticleCount η := by
  cases hLeft : η .left <;> cases hRight : η .right <;>
    simp [siteParticleCount, swapConfig, swapSite, hLeft, hRight]

def exclusionGenerator (observable : ExclusionConfig → Int)
    (η : ExclusionConfig) : Int :=
  observable (swapConfig η) - observable η

theorem exclusionGenerator_annihilates_particleCount (η : ExclusionConfig) :
    exclusionGenerator siteParticleCount η = 0 := by
  simp [exclusionGenerator, swapConfig_conserves_particles]

def occupationAt (site : ExclusionSite) (η : ExclusionConfig) : Int :=
  if η site then 1 else 0

def oneParticleGenerator (observable : ExclusionSite → Int)
    (site : ExclusionSite) : Int :=
  observable (swapSite site) - observable site

theorem oneSiteGenerator_duality (η : ExclusionConfig)
    (site : ExclusionSite) :
    exclusionGenerator (fun config => occupationAt site config) η =
      oneParticleGenerator (fun position => occupationAt position η) site := by
  rfl

end Book.Chapters.Chapter67
