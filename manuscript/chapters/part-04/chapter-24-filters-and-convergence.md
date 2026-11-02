# Chapter 24 — Filters and Convergence

> **Audience.** This chapter assumes familiarity with limits, continuity, and open sets. It introduces filters as Mathlib's shared language for sequences, neighborhoods, and eventual behavior, and develops proof patterns for `Tendsto` that avoid repeatedly expanding epsilon definitions.

Mathlib expresses many kinds of limiting behavior with filters. A sequence limit, a function limit, continuity at a point, and the statement that a property holds eventually all fit into the same framework. The benefit is not merely shorter notation: one theorem about filters can serve at infinity, near a point, along a subset, or under a map.

The main formalization skill is learning to change representations at the right boundary. Use `Tendsto` for general limits, neighborhood filters for topology, and `Eventually` for “for sufficiently large” statements. Convert to open sets or epsilon-delta statements only when that representation exposes the needed argument.

## Learning objectives

By the end of the chapter, you should be able to:

- interpret `Filter`, `Eventually`, and `Tendsto`;
- read the order on filters as refinement;
- express sequence convergence and continuity with filters;
- use eventual hypotheses with `filter_upwards`;
- move between filter maps, preimages, and convergence goals.

The examples use Mathlib's standard filter and topology notation. In a file that does not already open these namespaces, add:

```lean
open Filter Topology
```

## 1. A filter records which sets are eventually large

A filter on a type `α` is a collection of subsets of `α` that is closed under finite intersections and passage to supersets, and contains the whole type. Intuitively, it records which sets are “large” from the viewpoint relevant to a limiting question. The filter of tails on `Nat` records properties true for all sufficiently large natural numbers. The neighborhood filter at a point records sets that contain a neighborhood of that point.

The notation `s ∈ l` means that the set `s` is large according to filter `l`. A proposition is eventually true along `l` when the set of inputs where it holds belongs to the filter:

```lean
#check fun {α : Type*} (l : Filter α) (P : α → Prop) => ∀ᶠ x in l, P x
```

This notation can represent “for all sufficiently large `n`,” “for all points sufficiently close to `x`,” or “for all points in a chosen region,” depending on the filter. The quantifier stays uniform while the filter changes.

Common filters include:

- `atTop` on an ordered type, representing indices eventually above every bound;
- `cofinite`, representing all but finitely many elements;
- `pure a`, the principal filter concentrated at a point;
- `𝓝 x`, the neighborhood filter of a point in a topological space;
- `𝓝[s] x`, neighborhoods of `x` restricted to a set `s`.

The filter need not be proper: Lean's `Filter` also includes the bottom filter. When a proof needs a genuinely nontrivial filter, Mathlib typically asks for an instance such as `[l.NeBot]`. This distinction explains why some limit theorems require a nontriviality hypothesis while basic algebraic operations on filters do not.

The notation `∃ᶠ x in l, P x` says that `P` happens frequently along `l`. Along `atTop` on `Nat`, this means it is not eventually absent; along a neighborhood filter, it means it occurs arbitrarily close to the point. “Eventually” and “frequently” are dual ways of describing behavior relative to the same filter. They should not be confused with probability or with a count of how many inputs satisfy a condition: their meaning comes entirely from the chosen filter.

For `atTop`, `∀ᶠ n in atTop, P n` corresponds to the familiar form “there is a threshold after which `P` always holds.” For `cofinite`, it means `P` holds outside a finite exceptional set. For `𝓝 x`, it means that `P` holds throughout some neighborhood of `x`. This is the central abstraction: the proof manipulates eventual facts, while the filter determines what “eventual” means.

## 2. The order on filters measures refinement

The order on filters is reversed inclusion of their sets. `l₁ ≤ l₂` means that `l₁` is finer than `l₂`: every set eventually true for `l₂` is already eventually true for `l₁`. A finer filter makes a stronger demand about where inputs lie.

```text
finer filter          more sets count as eventual
     l₁ ≤ l₂       ⇒   every l₂-eventual property is l₁-eventual
```

For principal filters, this order corresponds to inclusion of the underlying sets. For neighborhoods, restricting to a side or a subset produces a finer filter than the unrestricted neighborhood filter. For sequences, `atTop` describes a directed approach in which bounds eventually hold.

This orientation is important when using monotonicity theorems. A limit along a coarser source filter implies the same limit along a finer source filter, because the finer filter discards at least as many inputs as “small.” In target filters, the direction is different: a limit into a finer target filter is a stronger conclusion.

If an inequality involving filters appears backwards, read it through eventual membership. Ask: which filter makes more sets eventual? This is more reliable than memorizing a slogan about “bigger” or “smaller” filters.

## 3. `Tendsto` unifies limits

For `f : α → β`, filters `l₁` on `α` and `l₂` on `β`, `Tendsto f l₁ l₂` says that every set large in the target pulls back to a set large in the source. Mathlib provides the characterization:

\[
  \operatorname{Tendsto}(f,l_1,l_2)
  \quad\Longleftrightarrow\quad
  \forall s \in l_2,\; f^{-1}(s) \in l_1.
\]

The direct Lean form is useful when a proof needs to reason about preimages:

```lean
example {α β : Type*} {f : α → β}
    {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ := by
  exact Filter.tendsto_def
```

The same predicate expresses several familiar ideas:

```text
sequence limit:       Tendsto u atTop (𝓝 x)
function limit:       Tendsto f (𝓝 x) (𝓝 y)
continuity at x:      Tendsto f (𝓝 x) (𝓝 (f x))
```

The target neighborhood filter is not special to real numbers. It works in any topological space. The source filter can also vary: `atTop` for sequences, `𝓝 x` for a limit at a point, or a neighborhood-within filter for a one-sided or restricted limit.

For real sequences, an epsilon-N definition says that for every positive tolerance `ε`, all terms after some index lie within `ε` of the proposed limit. The filter statement packages the same quantifiers: each neighborhood of the limit has a preimage that is eventual along `atTop`. The two formulations are equivalent when the topology has the usual metric basis, but the filter form extends immediately to spaces without a distance function. Use epsilon bounds when they expose estimates; use `Tendsto` when the theorem should be topological or apply to several kinds of source behavior.

## 4. A sequence that is eventually constant converges

One way to prove a sequence converges to `x` is to show it is eventually equal to the constant sequence at `x`:

```lean
example {u : Nat → Real} {x : Real}
    (h : ∀ᶠ n in atTop, u n = x) :
    Tendsto u atTop (𝓝 x) := by
  exact tendsto_nhds_of_eventually_eq h
```

This proof uses a library theorem that packages the neighborhood argument. An open set containing `x` also contains every term that is equal to `x`, and the eventual equality says that all sufficiently late terms have that value. The theorem lifts this reasoning to `Tendsto` without requiring the caller to unpack every neighborhood.

The constant sequence is an immediate special case:

```lean
example {X : Type*} [TopologicalSpace X] (x : X) :
    Tendsto (fun _ : Nat => x) atTop (𝓝 x) := by
  exact tendsto_const_nhds
```

These examples illustrate an important Mathlib habit: search for a theorem at the abstraction level of the goal. If the goal is a filter limit, use a `Tendsto` theorem. Unfolding neighborhoods should be reserved for proofs whose core argument genuinely concerns open sets.

## 5. Eventual statements compose like ordinary hypotheses

The tactic `filter_upwards` turns eventual propositions into a local proof context. Suppose `hP` says that `P x` holds eventually, and a pointwise implication turns `P x` into `Q x`. Then `Q` also holds eventually:

```lean
example {α : Type*} {l : Filter α} {P Q : α → Prop}
    (hP : ∀ᶠ x in l, P x)
    (hPQ : ∀ x, P x → Q x) :
    ∀ᶠ x in l, Q x := by
  filter_upwards [hP] with x hx
  exact hPQ x hx
```

The tactic selects an input satisfying the eventual hypotheses, then the proof continues pointwise. Multiple eventual facts can be combined in one call:

```lean
example {α : Type*} {l : Filter α} {P Q : α → Prop}
    (h₁ : ∀ᶠ x in l, P x) (h₂ : ∀ᶠ x in l, Q x) :
    ∀ᶠ x in l, P x ∧ Q x := by
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  exact ⟨hx₁, hx₂⟩
```

This is analogous to taking the intersection of the large sets on which each hypothesis holds. Filters are closed under finite intersections, so the combined context is available eventually.

For a complicated limit proof, separate the eventual part from the topological part. First show a pointwise estimate or equality holds eventually. Then use a `Tendsto` theorem to transfer it to the limit. This modular structure prevents an epsilon-delta proof from becoming a single block of nested quantifiers.

## 6. Maps of filters and Galois structure

The operation `Filter.map f l` pushes a filter forward along a function. It records which target sets have preimages that are large in `l`. The operation `Filter.comap f l` pulls a target filter back to the source. These operations form an order-theoretic adjunction, connecting this chapter to the Galois connections of Chapter 23.

The convergence predicate can be expressed as:

```text
Tendsto f l₁ l₂  ↔  Filter.map f l₁ ≤ l₂
```

Equivalently, it says the source filter is finer than the preimage of the target filter:

```text
Tendsto f l₁ l₂  ↔  l₁ ≤ Filter.comap f l₂
```

These forms are useful in different proofs. The `map` view emphasizes the behavior of the function on the source filter. The `comap` view emphasizes which source inputs are required to land in target neighborhoods. The preimage characterization from Section 3 is the elementwise version.

This connection also explains standard composition lemmas. If `f` tends to `l₂` and `g` sends `l₂` to `l₃`, then the composition sends the original source filter to `l₃`. Rather than proving preimage identities from scratch, apply the `Tendsto` composition theorem. For set maps and filters, inspect `map`/`comap` adjunction lemmas when the target is an order relation rather than a limit predicate.

The same method handles subsequences. If an index map `φ : Nat → Nat` tends to `atTop`, then composing a convergent sequence with `φ` preserves its limit. The proof is a composition of two `Tendsto` statements: the index map approaches infinity, and the original sequence approaches its limit along `atTop`. An increasing subsequence is one common way to establish the first statement, but the filter theorem needs only that `φ` tends to `atTop`.

## 7. Continuity is convergence at every point

Continuity at `x` is the special case in which both source and target filters are neighborhoods:

```lean
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} (h : ContinuousAt f x) :
    Tendsto f (𝓝 x) (𝓝 (f x)) := by
  exact h
```

This viewpoint supports generic proofs about continuous maps. If a function is continuous, limits can be pushed through it. If a sequence tends to `x`, continuity turns that into convergence of the image sequence to `f x`. The topological space instance determines what neighborhoods mean, while the proof uses a common filter interface.

When a continuity goal looks difficult, inspect whether it can be reframed as a `Tendsto` goal or discharged by composition. Conversely, when a general convergence theorem needs continuity, use the `ContinuousAt` or `Continuous` hypothesis at the point where neighborhood filters are introduced.

The filter formulation also handles continuity within a set, one-sided continuity, and convergence along subspaces. These variants change the source filter rather than requiring a new definition of limit. That uniformity is one of the main reasons Mathlib phrases much of topology in filter language.

For example, the right-hand limit of a real function at `x` uses the neighborhood filter restricted to points greater than `x`. Its target remains the ordinary neighborhood filter at the proposed limit. The proof can therefore reuse the same composition and monotonicity theorems as a two-sided limit; only the source filter records the restriction. When searching Mathlib, try the `Tendsto` theorem first and then identify the appropriate `nhdsWithin` notation.

## 8. Common failure modes

### The filter inequality is oriented incorrectly

Translate it into eventual membership. Remember that `l₁ ≤ l₂` means `l₁` is finer, so every `l₂`-eventual set is `l₁`-eventual.

### A proof unfolds `nhds` too early

Search for a theorem about `Tendsto`, `Eventually`, or continuity first. Use open sets when the proof needs an open neighborhood argument, not as a reflexive first step.

### `Eventually` hypotheses are not available at the same input

Combine them with `filter_upwards [h₁, h₂]`. Closure under finite intersections is precisely what makes this possible.

### A filter is assumed nontrivial without evidence

Check whether the theorem requires `[l.NeBot]`. The bottom filter is allowed by the general `Filter` type, and some statements are false or degenerate for it.

### A one-sided limit is treated as a separate topology

Use `nhdsWithin` or the standard one-sided neighborhood notation. It changes the source filter and often lets the ordinary `Tendsto` API apply.

## 9. A workflow for limit proofs

1. Identify the source behavior: `atTop`, `cofinite`, a neighborhood, or a restricted neighborhood.
2. State the goal with `Tendsto` rather than immediately expanding to open sets or epsilon bounds.
3. Look for library lemmas about constant functions, eventual equality, composition, or continuity.
4. Use `filter_upwards` to combine eventual hypotheses and prove local pointwise facts.
5. Convert to preimages or `map`/`comap` only when the order-theoretic view simplifies the goal.
6. Add `NeBot` assumptions only where the mathematical statement requires a nontrivial filter.
7. Unfold neighborhoods as a final step when the local topological basis is the actual content of the proof.

This workflow leaves the proof at the highest useful abstraction level. It is easier to reuse, less sensitive to the chosen topology, and usually shorter than rebuilding epsilon-delta reasoning for every theorem.

## 10. Exercises

1. State the convergence of a sequence `u : Nat → X` to `x` using `Tendsto` and explain the roles of `atTop` and `𝓝 x`.
2. Prove that eventual equality to a constant implies convergence, first with a library theorem and then by unfolding the neighborhood filter.
3. Use `filter_upwards` to combine two eventually true inequalities and derive an eventual third inequality.
4. Explain the order orientation for filters using the statement that a one-sided neighborhood filter is finer than an unrestricted neighborhood filter.
5. Rewrite a `Tendsto` goal using `Filter.tendsto_def` and identify the preimage set in the source.
6. Show how continuity at a point is a `Tendsto` statement. Then use continuity to transport a sequence limit through a function.
7. Find a theorem requiring `NeBot` and explain why the conclusion can fail for the bottom filter.

### Selected exercises, formalized

The first proof of Exercise 2 uses Mathlib's convergence theorem. The second proves the same result from the preimage characterization of `Tendsto` and the fact that every neighborhood contains its center:

```lean
theorem exercise_24_2_via_library
    {X : Type*} [TopologicalSpace X] {u : Nat → X} {x : X}
    (h : ∀ᶠ n in atTop, u n = x) :
    Tendsto u atTop (𝓝 x) := by
  exact tendsto_nhds_of_eventually_eq h

theorem exercise_24_2_via_neighborhoods
    {X : Type*} [TopologicalSpace X] {u : Nat → X} {x : X}
    (h : ∀ᶠ n in atTop, u n = x) :
    Tendsto u atTop (𝓝 x) := by
  rw [Filter.tendsto_def]
  intro s hs
  have hx : x ∈ s := mem_of_mem_nhds hs
  filter_upwards [h] with n hn
  change u n ∈ s
  rw [hn]
  exact hx
```

Exercise 3 is the transitivity of an eventual inequality. Combining the two eventual hypotheses gives a pointwise proof context, where ordinary transitivity closes the goal:

```lean
theorem exercise_24_3_eventually_le_trans
    {α β : Type*} {l : Filter α} [Preorder β]
    {f g h : α → β}
    (hfg : ∀ᶠ x in l, f x ≤ g x)
    (hgh : ∀ᶠ x in l, g x ≤ h x) :
    ∀ᶠ x in l, f x ≤ h x := by
  filter_upwards [hfg, hgh] with x hxfg hxgh
  exact le_trans hxfg hxgh
```

For Exercise 4, the Mathlib order on filters records that restricting neighborhoods to a set gives a finer filter. Taking the set to be the strict right ray gives the one-sided case. Exercise 5 is the preimage characterization of `Tendsto`:

```lean
theorem exercise_24_4_right_neighborhood_is_finer (x : ℝ) :
    𝓝[Set.Ioi x] x ≤ 𝓝 x := by
  exact nhdsWithin_le_nhds

theorem exercise_24_5_tendsto_preimage
    {α β : Type*} {f : α → β}
    {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Filter.tendsto_def
```

For Exercise 6, compose the sequence's limit with continuity at its limit point:

```lean
theorem exercise_24_6_continuous_map_of_sequence_limit
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} {u : Nat → X}
    (hlim : Tendsto u atTop (𝓝 x)) (hcont : ContinuousAt f x) :
    Tendsto (f ∘ u) atTop (𝓝 (f x)) := by
  have hmap : Tendsto f (𝓝 x) (𝓝 (f x)) := hcont
  exact hmap.comp hlim
```

Exercise 7 uses a theorem whose nontrivial-filter assumption is essential. Every filter-large set is nonempty for a `NeBot` filter. The bottom filter contains the empty set, so the implication is false there:

```lean
theorem exercise_24_7_mem_of_neBot_is_nonempty
    {α : Type*} {l : Filter α} [NeBot l] {s : Set α}
    (hs : s ∈ l) : s.Nonempty :=
  Filter.nonempty_of_mem hs

example : (∅ : Set Nat) ∈ (⊥ : Filter Nat) := by simp

example : ¬ (∅ : Set Nat).Nonempty := by simp
```

## Summary

Filters encode which sets are large for a limiting question. `Eventually` states that a property holds on a filter-large set, and `Tendsto` says target neighborhoods pull back to source-large sets. The order `l₁ ≤ l₂` means `l₁` is finer. Use `atTop` for sequences, `𝓝 x` for neighborhoods, and `filter_upwards` to combine eventual hypotheses. Filter `map` and `comap` expose the order-theoretic structure behind convergence, while continuity is a special case of `Tendsto`.

## Further reading

- [Mathlib: Filters in topology](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html)
- [Mathlib: `Tendsto` and filter operations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Tendsto.html)
- [Mathlib: Neighborhood filters](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Neighborhoods.html)
- [Mathematics in Lean: Topology](https://leanprover-community.github.io/mathematics_in_lean/C11_Topology.html)
