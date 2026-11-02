# Chapter 44 — Irreducible Markov Kernels

> **Audience.** This chapter assumes familiarity with Markov kernels, kernel composition, probability measures, and invariant distributions. It develops measure-relative irreducibility as a reachability property of repeated transitions.

A transition kernel describes one random step. Its powers describe repeated steps. Irreducibility asks whether every set that is large according to a reference measure can eventually be reached from every starting state with positive probability. This is a global property assembled from local transitions, and it is one of the basic structural hypotheses in Markov-chain theory.

Mathlib defines irreducibility directly for kernels rather than requiring a particular bundled path process. The definition refers to a reference measure `φ` and to the mass that a finite-step kernel assigns to measurable sets. This makes the statement portable between finite-state chains, countable chains, and more general measurable state spaces.

The formalization lesson is to separate three ingredients: the transition kernel, the reference measure that defines which sets count as significant, and the finite-step reachability proof. Irreducibility alone does not imply convergence to a stationary law; further hypotheses such as recurrence, aperiodicity, or tightness may be needed for those conclusions.

## Learning objectives

By the end of the chapter, you should be able to:

- state `Kernel.IsIrreducible φ κ` in terms of kernel powers;
- explain why irreducibility depends on a reference measure;
- prove finite-state irreducibility from connectivity of the transition graph;
- identify trivial or vacuous reference measures;
- use monotonicity with respect to the reference measure;
- distinguish reachability from recurrence and convergence.

## 1. Reachability through kernel powers

Let `κ : Kernel α α` be a transition kernel on one state space, and let `φ` be a measure on that space. The kernel is `φ`-irreducible if for every measurable set `A` with `φ A > 0` and every initial state `a`, some finite-step kernel gives `A` positive mass:

\[
  \forall A,\quad \phi(A)>0\Longrightarrow
  \forall a,\quad \exists n\in\mathbb{N},\; (\kappa^n)(a)(A)>0.
\]

Mathlib packages this as `ProbabilityTheory.Kernel.IsIrreducible φ κ`; `isIrreducible_iff` exposes the quantified formulation. Kernel powers are formed by repeated composition, so the statement reduces a long-time property to the algebra of kernel composition.

The reference measure matters. It determines which target sets must be reachable. If `φ` is counting measure on a finite state space, every nonempty set has positive measure, so irreducibility means every state can reach every nonempty target with positive probability in some finite number of steps. For a continuous state space, the reference measure can ignore sets of measure zero, and irreducibility need not require reaching every individual point.

```text
state a ──κ──▶ possible next states ──κ──▶ ... ──κⁿ──▶ target A
                                                      φ(A) > 0
irreducible: every start has some finite n with positive target mass
```

The exponent `n` may depend on both the starting state and target set. Irreducibility does not usually assert that a single fixed time works for every pair.

The reference measure can focus attention on only part of the state space. If `φ` is supported on a subset, targets disjoint from that support impose no condition, though every starting state is still tested. For example, a chain may be required to reach every positive-volume region without being required to assign positive mass to a particular point. In finite spaces with counting measure, every point is a positive-measure target, recovering the stronger graph reachability condition.

## 2. Worked example: a finite strongly connected graph

Let `α` be a finite state space and draw a directed edge `a → b` whenever the transition probability `κ a {b}` is positive. Equip `α` with counting measure. If the directed graph is strongly connected, then for every pair of states `a,b` there is a finite path from `a` to `b` whose every edge has positive probability.

The probability of following that particular path is the product of its positive edge probabilities, so it is positive. Therefore, for every nonempty target `A`, choose any `b ∈ A`; a path from `a` to `b` gives positive probability for `κ^n a A`. This proves irreducibility with respect to counting measure.

In Lean, represent states by a finite type and prove a path lemma from graph connectivity. Then show that a path of length `n` contributes a positive summand to the iterated transition probability. The kernel composition formula expands the finite-step transition over intermediate states; positivity of one path term is enough to prove the total mass is positive.

The reverse implication also holds for a finite transition graph: if every state can reach every nonempty set with positive probability, then every singleton target is reachable, so the graph is strongly connected. Thus finite-state kernel irreducibility recovers the usual graph-theoretic criterion.

Conversely, if the graph is not strongly connected, choose states `a` and `b` with no directed path from `a` to `b`. The singleton `{b}` has positive counting measure, but every finite-step transition from `a` assigns it zero mass. This gives a direct counterexample to the quantified irreducibility predicate and is often the shortest way to formalize failure of irreducibility.

For a finite strongly connected graph, repeated vertices can be removed from a path without breaking its endpoints. Therefore, for distinct states, a simple path has length at most `|α|-1`; the source-to-itself case uses the zero-step path or a positive-length cycle as required by the chosen convention. This gives a finite bound on the witness length in finite state spaces, although the definition itself does not request that bound. If a later theorem needs uniformity in the starting state, finiteness can be used to take a maximum over finitely many pairs.

## 3. Worked example: an absorbing state

Consider states `{0,1}` with transitions `0 → 0` and `1 → 0` always. State `1` is transient in one step and state `0` is absorbing. With counting measure, the singleton `{1}` has positive measure, but from starting state `0` it is never reached. The kernel is therefore not irreducible.

This example can be formalized without a path process. The zero-step and one-step cases are explicit; for any larger `n`, kernel composition shows the transition remains concentrated at `0`. The proof has two layers: compute the kernel powers or establish the absorbing-state invariant, then apply the irreducibility characterization to the target `{1}`.

It also shows why the starting state is universally quantified. A state may be reachable from one part of a chain but not from another. An irreducibility proof must handle every starting point, not only states in the support of a convenient initial distribution unless the theorem has been restricted accordingly.

## 4. Dependence on the reference measure

If `φ₁ ≤ φ₂` as measures and `κ` is `φ₂`-irreducible, then it is also `φ₁`-irreducible. Every set positive under `φ₁` is positive under `φ₂`, so the larger collection of target sets required by `φ₂`-irreducibility includes those needed for `φ₁`.

Mathlib provides `Kernel.isIrreducible_of_le_measure` for this monotonicity. It is useful when a theorem establishes irreducibility with respect to a convenient measure and an application needs a weaker reference measure, such as a submeasure supported on a subset.

The zero measure is an important edge case. It assigns no positive mass to any set, so the universal condition on positive-measure target sets is vacuous. A statement of irreducibility with respect to `0` carries no reachability information. In applications, make the reference measure meaningful—often a stationary measure, a nonzero measure, or counting measure on a finite state space.

Scaling a reference measure by a positive finite constant does not change which sets have positive measure and therefore does not change irreducibility. Mathlib includes an instance for scalar multiples. More generally, equivalent measures with the same null sets yield the same positive target sets and the same irreducibility notion.

When transferring irreducibility between models, state the measure comparison in the direction required by the theorem. To pass from `φ₂`-irreducibility to `φ₁`-irreducibility, prove `φ₁ ≤ φ₂`; the reverse comparison does not suffice. For equivalent measures, establish both absolute-continuity directions if the goal is an equivalence of irreducibility statements.

## 5. Irreducibility and stationary distributions

An invariant probability measure `π` satisfies `π ∘ₘ κ = π`, as introduced in Chapter 40. Irreducibility is often studied together with such an invariant measure, but the two properties are logically distinct. A kernel can be irreducible without a finite invariant probability measure, especially on an infinite state space. A kernel can also have an invariant measure while decomposing into multiple closed communicating classes.

In finite state spaces, every Markov chain has at least one stationary distribution. Irreducibility then implies uniqueness of the stationary distribution, though convergence of the law to it generally also requires aperiodicity. These are finite-state probabilistic theorems; the `Kernel.IsIrreducible` definition alone does not supply all those conclusions.

This separation matters in formal proofs. First prove the invariant-measure equation with kernel composition. Separately establish irreducibility from reachability. Only then apply a theorem whose statement explicitly combines them with any additional hypotheses. Do not infer uniqueness or convergence from the irreducibility predicate alone.

Periodicity is a separate obstruction to convergence. The two-state chain that alternates deterministically between `0` and `1` is irreducible on the finite state space and has the uniform stationary distribution. Yet, when started at `0`, its distribution alternates between the point mass at `0` and the point mass at `1`; it does not converge to the stationary law. Aperiodicity or a suitable time-averaged conclusion is needed for stronger limit statements.

## 6. Kernel powers and proof strategy

The power `κ ^ n` is repeated kernel composition. For a target set `A`, the quantity `(κ ^ n) a A` is the probability of being in `A` after `n` steps when starting at `a`. The exact expansion into a sum or integral over intermediate states depends on the state space: finite sums for finite chains, countable sums for countable spaces, and iterated integrals for general kernels.

For finite-state proofs, establish positivity by selecting one path and showing its contribution survives the sum. For analytic state spaces, use support or positivity lemmas for integrals and compositions. In both cases, isolate a reusable lemma that propagates positive transition mass along a finite sequence; the final irreducibility proof then reduces to choosing a path or a finite-step witness.

In a finite state space, the propagation lemma can be proved by induction on path length. The base case is the identity transition at length zero. For the inductive step, compose the first transition with the remaining kernel power and use the finite sum over the intermediate state. The summand associated with the path's next vertex is positive, while all other summands are nonnegative, so the full sum is positive. This proof mirrors the mathematical path argument and gives a reusable bridge from graph connectivity to a kernel-power estimate.

The number of steps can vary with the target and initial point. Therefore, a proof that gives a uniform transition time is stronger than required. It may be worthwhile when available, but do not add a uniformity goal unless the application needs one.

One reusable way to organize a finite proof is to define `R n a` as the set of states reachable from `a` with positive probability in at most `n` steps. The recurrence for `R (n+1) a` adds states reached by one positive transition from `R n a`. Graph connectivity then proves every target state belongs to some `R n a`. A separate lemma converts membership in `R n a` into positive mass for a suitable kernel power. This separates combinatorial path construction from measure-valued composition and is easier to maintain than repeatedly expanding powers in the final irreducibility proof.

## 7. API scope and proof workflow

The current Mathlib interface is deliberately compact: `IsIrreducible` and its equivalence characterize positive-probability reachability, and `isIrreducible_of_le_measure` transfers the property across ordered reference measures. The surrounding kernel API supplies composition and powers. Large theorems about recurrence classifications, mixing rates, or convergence of distributions require additional structures and should not be inferred just from this definition.

A practical proof order is:

1. Choose the state measurable space, transition kernel, and reference measure.
2. Prove the kernel is Markov when probability normalization is needed.
3. Translate the target into a measurable set with positive `φ`-measure.
4. Construct a finite path or another finite-step reachability witness.
5. Use kernel composition to show the path contributes positive target mass.
6. Apply `isIrreducible_iff` to assemble the universal property.
7. Keep stationarity, recurrence, and convergence hypotheses as separate lemmas.

For countable state spaces, the same structure applies, but a kernel-power value is an infinite sum and positivity must be obtained from one positive path term without assuming that the sum is finite. For continuous spaces, a single path through exact points may have probability zero; use positive-measure neighborhoods or support conditions instead. The abstract irreducibility definition is deliberately flexible enough to accommodate these different proof styles.

This organization distinguishes graph combinatorics from measure theory. The path argument proves reachability; the kernel theorem converts it to positive probability; the irreducibility predicate packages the result for later theorems.

## 8. Common failure modes

### The reference measure is omitted

Irreducibility is always relative to `φ`. Specify which sets must be reachable.

### Point reachability is required in a continuous space

The target condition concerns every positive-measure measurable set, not every singleton.

### One starting state is checked

Irreducibility quantifies over all states. A result only for an initial distribution's support is weaker.

### A zero reference measure is accepted accidentally

Irreducibility then holds vacuously. Establish that the chosen reference measure is nonzero or otherwise meaningful.

### Irreducibility is treated as convergence

Irreducibility alone does not imply a unique stationary law or convergence to equilibrium. Additional hypotheses are needed.

### The wrong power orientation is used

Kernel powers represent repeated composition. Check the intermediate-state integral or finite sum when expanding `κ ^ n`.

## 9. Exercises

1. State `Kernel.IsIrreducible φ κ` using measurable sets and kernel powers.
2. Explain how the reference measure determines which targets matter.
3. Prove that a strongly connected finite transition graph yields irreducibility with counting measure.
4. Show that the absorbing-state example is not irreducible.
5. Prove monotonicity of irreducibility when replacing `φ₂` by a measure `φ₁ ≤ φ₂`.
6. Explain why irreducibility with respect to the zero measure is vacuous.
7. Distinguish irreducibility, existence of an invariant probability, and convergence to equilibrium.
8. For a finite chain, identify the graph property corresponding to kernel irreducibility.
9. Outline how a positive-probability path gives a positive term in a kernel-power expansion.
10. Locate `isIrreducible_iff` and `isIrreducible_of_le_measure` in Mathlib's documentation.

## Summary

Kernel irreducibility means every measurable target set of positive reference-measure mass is reachable from every state with positive probability in some finite number of steps. The property depends on the reference measure and is proved by combining finite-step kernel composition with reachability arguments. In finite chains it corresponds to strong connectivity of the transition graph. It is distinct from recurrence, stationarity, and convergence, which require additional hypotheses.

## Further reading

- [Mathlib: Irreducible kernels](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Irreducible.html)
- [Mathlib: Kernel composition and powers](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html)
- Chapter 40 for transition kernels, Chapter 43 for conditional independence of Markov processes, and Chapter 45 for invariant and reversible kernels.
