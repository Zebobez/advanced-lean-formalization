# Chapter 27 — Compactness and Completeness

> **Audience.** This chapter assumes familiarity with topological spaces, metric spaces, compact sets, and Cauchy sequences. It develops proof strategies for compactness and completeness using Mathlib's existing topological and filter interfaces.

Compactness is often introduced through open covers, while analysis proofs frequently use sequences and filters. Mathlib supports both views. The formalization task is to choose the one that matches the theorem's structure, then use the library bridge between them when needed. Completeness follows a similar pattern: state Cauchy behavior through the standard interface and let a `CompleteSpace` hypothesis supply the limit.

This chapter extends the filter vocabulary of Chapter 24. It emphasizes how compactness turns local or eventual information into finite or global conclusions, how continuity transports compactness, and how properness and completeness assumptions should appear in theorem statements.

## Learning objectives

By the end of the chapter, you should be able to:

- use `IsCompact` without unfolding its open-cover definition unnecessarily;
- transfer compactness along continuous maps and closed subsets;
- choose between open-cover, filter, and sequential arguments;
- state Cauchy and completeness results through standard Mathlib interfaces;
- track the topological assumptions required by compactness theorems.

## 1. Compactness has more than one useful view

In general topology, a set is compact if every open cover has a finite subcover. In metric spaces, compactness is also characterized by sequential compactness: every sequence has a convergent subsequence with limit in the set. Compactness can also be described through filters and cluster points.

```text
open-cover view       every cover → finite subcover
sequence view         every sequence → convergent subsequence
filter view           every nontrivial filter → cluster behavior
```

The formulations are equivalent under appropriate hypotheses, but a proof should not move between them without a reason. Use open covers when the argument constructs a cover or chooses a finite subcover. Use filters when the theorem concerns limits, cluster points, or eventual behavior. Use sequences in metric arguments when an explicit sequence or subsequence is already available.

Mathlib records compactness with `IsCompact s`. This proposition is the public interface. Most theorems should take `hs : IsCompact s` and apply a result about images, closed subsets, extrema, or cluster points. Unfold the definition only when the finite-subcover construction itself is the mathematical argument.

When the open-cover definition is the argument, name the cover and its index type explicitly. A typical proof has four pieces: an indexed family of open sets, a proof that the family covers `s`, compactness to obtain a finite set of indices, and a proof that those finitely many sets still cover `s`. Keeping the cover and finite index set named avoids nested existential goals and makes the use of compactness visible. For a subbasis theorem, first verify that the cover elements belong to the chosen subbasis; the finite-subcover conclusion then follows from the specialized theorem.

The index type is not required to be finite in advance. Compactness produces finiteness of a subcollection of indices. This differs from a `Fintype` assumption, which supplies an enumeration of the whole index type. If a proof expects a finite cover but asks for `Fintype` of all possible open sets, it is likely using a lower-level representation than needed.

This distinction also helps organize the proof state. Keep the cover as a function `i ↦ U i` and its covering hypothesis as a named proposition. Once compactness is applied, Lean returns a finite set of indices; the rest of the proof is a pointwise verification that each point is covered by one selected member. Naming these pieces prevents a goal from becoming a large nested expression involving `Set.range`, unions, and existential witnesses all at once.

## 2. Continuous images preserve compactness

If `s` is compact and `f` is continuous, then `f '' s` is compact. This is a recurring reusable theorem:

```lean
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsCompact s) {f : X → Y}
    (hf : Continuous f) : IsCompact (f '' s) := by
  exact hs.image hf
```

The proof is short because all topological details are inside the theorem. If the function is only continuous on `s`, use the version for `ContinuousOn`. If the map is an embedding or homeomorphism, stronger equivalences can move compactness in both directions.

This interface encourages a clean proof design. First prove continuity of the map with the `continuity` tactic or local lemmas. Then transfer compactness with `hs.image hf`. Avoid proving that every open cover of the image pulls back to a cover of the source unless the open-cover argument is needed for a specialized result.

Compactness is stable under continuous maps because an open cover of the image pulls back to an open cover of the compact source. The finite subcover of the source then maps back to a finite subcover of the image. The theorem captures this reasoning once for every topological space.

## 3. Closed subsets and Hausdorff separation

A closed subset of a compact set is compact. In Lean, one usually starts with `hs : IsCompact s`, `ht : IsClosed t`, and `hts : t ⊆ s`, then applies the corresponding theorem. This is useful when compactness has already been established for an ambient set but the goal concerns a constrained region inside it.

In Hausdorff spaces, compact sets are closed. The Hausdorff assumption matters: without separation, compactness does not imply closedness. Lean makes the boundary explicit through a typeclass such as `[T2Space X]`. If a proof of closedness fails because no separation hypothesis is available, check whether the theorem is actually true in the stated topological space.

The same assumption tracking appears in uniqueness results. Limits are unique in Hausdorff spaces, and compactness can help identify cluster points. When several topological facts are combined, state the weakest separation assumption needed by each step rather than adding a global stronger topology without explanation.

## 4. Heine–Borel through the space's properness

In Euclidean space, closed and bounded sets are compact. Mathlib expresses this through a general theorem for proper metric spaces. A metric space is proper when its closed bounded sets are compact; the real line and finite-dimensional normed spaces over complete fields provide standard examples.

```lean
example {s : Set ℝ} (hc : IsClosed s)
    (hb : Bornology.IsBounded s) : IsCompact s := by
  exact Metric.isCompact_of_isClosed_isBounded hc hb
```

This theorem's assumptions are meaningful. A general metric space need not have every closed bounded set compact. If the proof is intended to work in an arbitrary metric space, the conclusion needs an additional condition such as properness or finite-dimensionality. The specialized theorem for `ℝ` works because the required proper-space instance is available.

When a typeclass is not found, inspect which property the theorem expects: `ProperSpace`, `FiniteDimensional`, or another structural assumption. Do not replace a missing instance with a broad classical argument; the obstacle may be that the mathematical theorem is false for the current space.

## 5. Compactness transfers bounds and extrema

A continuous real-valued function on a nonempty compact set is bounded and attains its minimum and maximum. In a proof, these are often separate steps: establish compactness of the image, then use completeness or order structure of the codomain to find an extremum. Mathlib provides the resulting theorems so users do not need to construct convergent subsequences manually.

The empty-set hypothesis is important for attainment. A function on an empty set has a compact image, but there is no point at which a maximum is attained. Lean represents this distinction with an explicit nonemptiness hypothesis in the extreme-value theorem.

For an abstract order-valued codomain, the relevant assumptions may be a conditionally complete order and a topology compatible with its order. A theorem over `ℝ` can often use the standard real instances, while a reusable theorem should state the order and topological conditions explicitly.

The formalization strategy is:

1. prove `IsCompact s`;
2. prove `ContinuousOn f s`;
3. establish `s.Nonempty` if attainment is required;
4. apply the compact image or extreme-value theorem;
5. extract the point and property from the existential conclusion.

Keeping these hypotheses named makes the theorem's mathematical prerequisites visible and localizes failures when one condition is missing.

## 6. Compactness through filters and cluster points

Chapter 24 introduced `Tendsto`, `Eventually`, and neighborhood filters. Compactness interacts with this language by guaranteeing cluster points for appropriate nontrivial filters contained in a compact set. This is valuable when a proof is already phrased in terms of limits or eventual membership.

For a sequence in a compact set, the filter generated by its tails has cluster behavior. In a metric space, that cluster point can be used to construct a convergent subsequence. The filter theorem is more general than the sequential theorem because it does not assume the source is `Nat` or that the topology is first countable.

Use the filter route when the theorem naturally involves a net, a directed set, or a general filter. Use a sequential compactness theorem when the constructed object is explicitly a sequence and the metric setting supplies the equivalence. Do not convert a general compactness result into sequences unless the space has the hypotheses needed for that conversion.

The nontriviality condition `[l.NeBot]` is not decorative. The bottom filter has every set as eventual, so it can satisfy degenerate filter inequalities without representing any genuine accumulation behavior. Compactness theorems about cluster points therefore need to exclude that case.

For a sequence in a compact subset of a metric space, the sequential formulation is often the most concrete. Starting from the sequence, first use the compactness theorem to obtain a cluster point or a convergent subsequence. Then show the limit remains in the set using closedness, if that is not already part of the theorem's conclusion. In a general topological space, a sequence may not detect every compactness phenomenon; the filter formulation avoids assuming that sequences determine the topology.

When both the sequence and its image under a continuous function are present, it can be shorter to use `Tendsto` composition and compact image results than to extract a subsequence. The right proof view depends on the desired output: subsequences provide an explicit convergent sequence; compact image and filter arguments often give existence without constructing one.

As a practical rule, inspect the conclusion before choosing a formulation. If it asks for a subsequence, use sequential compactness. If it asks for a point that meets every neighborhood condition, a cluster-point theorem may fit directly. If it asks for compactness of an image, do not introduce a sequence at all: use continuity and `IsCompact.image`. Moving into a lower-level formulation is useful only when it exposes information the current interface does not provide.

## 7. Completeness and Cauchy behavior

A metric or uniform space is complete when every Cauchy filter converges. In a metric setting, Cauchy sequences are the familiar special case. Lean's `CompleteSpace` typeclass records completeness, and Cauchy behavior is expressed through the metric or uniform-space interface.

When proving that a sequence converges, separate two tasks: show it is Cauchy, then invoke completeness. The Cauchy proof uses distance estimates and eventual bounds. The completeness theorem supplies the limit. This separation allows the same Cauchy estimate to be reused in any complete space that has the appropriate metric structure.

```text
estimate distances between late terms
                 │
                 ▼
             Cauchy sequence
                 │ CompleteSpace
                 ▼
                 limit exists
```

For example, in any complete uniform space, the standard theorem converts a `CauchySeq u` into an existential limit with a `Tendsto` conclusion. The proof script can therefore remain short once the pairwise distance estimate is established. The limit is existential because the completeness statement need not choose a canonical point; if a particular limit is required, use uniqueness in a separated space to identify it with the candidate.

For real numbers, completeness is already available. For a subspace, function space, or quotient construction, completeness may require a separate theorem. Do not assume that a subtype inherits completeness merely because the ambient space is complete; the subset may need to be closed or otherwise satisfy a completeness criterion.

For a direct use of completeness, the proof state should separate the Cauchy fact from the convergence fact. The standard theorem `cauchySeq_tendsto_of_complete` accepts a Cauchy sequence in a complete uniform space and yields an existential limit together with `Tendsto`. In a metric proof, first establish the uniform Cauchy condition from the distance estimate. Then apply the completeness theorem and use the returned convergence property. If a later argument has already named a candidate limit, uniqueness of limits in a separated space identifies the existential limit with that candidate.

## 8. Completeness and closed subspaces

A closed subset of a complete metric space is complete with the subtype metric. This theorem is a common way to establish completeness of a space defined by constraints. First show the carrier is closed; then use the inherited metric-space structure and the closed-subspace completeness theorem.

Conversely, completeness of a subset may imply it is closed under suitable ambient assumptions, such as a metric space. These theorems are useful in analysis, but their exact hypotheses vary with the structure involved. Read whether the result asks for a closed set, a complete subspace, or a nonempty set; do not rely on a remembered statement from a different setting.

If the subset is a subtype such as a closed interval, compact set, or solution space, typeclass inference may already know its topology and metric. The completeness theorem then applies to the subtype. If it does not, check whether the carrier is actually closed, whether the topology is induced, and whether the scalar or ambient space is complete.

## 9. Common failure modes

### Compactness is unfolded into open-cover details too early

Search for a theorem about `IsCompact`, images, closed subsets, or extrema first. Unfold only when finite subcovers are central.

### A bounded closed set is claimed compact in an arbitrary metric space

Check the proper-space or finite-dimensional hypotheses. Heine–Borel does not hold in every metric space.

### An extremum theorem has an unsolved nonemptiness condition

Prove `s.Nonempty` explicitly. Compactness alone does not provide a point in an empty set.

### A sequence argument is used in a nonmetrizable space

Use the filter formulation unless countability or a metric theorem justifies the sequential characterization.

### Completeness is inferred for an arbitrary subtype

Prove the subset is closed or use the correct completeness theorem for its structure. Completeness does not automatically pass to every subset.

## 10. Exercises

1. Prove that a continuous image of a compact set is compact using `IsCompact.image`. Then state how the proof changes for `ContinuousOn`.
2. Use Heine–Borel to prove compactness of a closed bounded subset of `ℝ`. Identify which assumption would be missing in an arbitrary metric space.
3. Prove that a closed subset of a compact set is compact. Compare the theorem application with an open-cover proof.
4. Find the Mathlib theorem stating that a continuous function on a nonempty compact set attains a maximum. List its hypotheses and explain the role of nonemptiness.
5. State compactness using a filter or cluster-point theorem and explain why a `NeBot` assumption is needed.
6. Show that a Cauchy sequence in a complete space converges using the standard completeness theorem. Keep the Cauchy estimate separate from the limit argument.
7. Prove completeness of a closed subtype of a complete metric space using the library interface.

## Summary

Use `IsCompact` as the public interface and select the open-cover, sequence, or filter view according to the theorem. Continuous images and closed subsets preserve compactness; closed bounded sets are compact under proper-space hypotheses such as the usual real topology. Compactness yields bounds, extrema, and cluster points, with nonemptiness and nontriviality assumptions made explicit. To use completeness, first prove Cauchy behavior, then invoke `CompleteSpace`; for subtypes, establish the appropriate closedness condition.

## Further reading

- [Mathlib: Compact sets and compact spaces](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html)
- [Mathlib: Heine–Borel for proper metric spaces](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Bounded.html)
- [Mathematics in Lean: Topology and compactness](https://leanprover-community.github.io/mathematics_in_lean/C11_Topology.html)
- [Mathlib: Completeness and Cauchy structures](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Cauchy.html)
