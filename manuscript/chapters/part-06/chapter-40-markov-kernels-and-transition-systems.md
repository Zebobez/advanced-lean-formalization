# Chapter 40 — Markov Kernels and Transition Systems

> **Audience.** This chapter assumes familiarity with probability measures, measurable maps, product integration, and conditional expectation. It develops Markov kernels as measurable families of transition measures and shows how kernel composition represents repeated random transitions.

A deterministic state-transition function sends each state to one next state. A random transition assigns a probability distribution of possible next states to each current state. The right formal object is a Markov kernel: a measurable map from the current state space to probability measures on the next state space.

This interface separates a one-step transition rule from any particular initial distribution or sample-path construction. Once the kernel is defined, measures can be transported through it, kernels can be composed, and repeated transitions can be expressed with kernel powers. Mathlib provides these measure-theoretic building blocks; a path-space process and its Markov property can then be assembled from kernels, filtrations, and conditional expectations.

The chapter focuses on this reusable kernel layer. It does not assume that every application already has a bundled “Markov chain” object. In many formalizations, the cleanest representation is a state space, an initial measure, a Markov kernel, and lemmas describing how one-step and multi-step laws are computed.

## Learning objectives

By the end of the chapter, you should be able to:

- define a kernel as a measurable family of measures;
- distinguish a general kernel from a Markov kernel;
- compose transition kernels and read the order of composition;
- evolve an initial measure by binding it with a kernel;
- translate a finite transition matrix into a kernel calculation;
- recognize the API boundary between kernels and path-space Markov processes.

## 1. A kernel is a family of measures

Let `α` be a measurable space of current states and `β` a measurable space of next states. A kernel `κ : Kernel α β` assigns a measure `κ a` on `β` to each `a : α`, and for every measurable set `s ⊆ β`, the function

\[
  a\longmapsto \kappa(a)(s)
\]

is measurable. The measurability condition lets the transition probability vary measurably with the current state.

A Markov kernel additionally satisfies that `κ a` is a probability measure for every state `a`. Mathlib calls this property `IsMarkovKernel κ`. The kernel structure packages measurability; the typeclass records normalization. This split is useful because some kernel constructions are merely finite or s-finite, while probability transition rules need total mass one.

```text
current state a ──▶ measure κ a on next states
       │                         │
       └──── measurable dependence on a ────▶ Markov kernel
```

For a finite state space, the kernel is a transition matrix whose rows sum to one. For a continuous state space, each row is a probability measure and the state-to-event probability map remains measurable.

## 2. Deterministic transitions as kernels

Every measurable function `f : α → β` gives a deterministic kernel: at state `a`, place a Dirac probability measure at `f a`. Mathlib exposes this as `Kernel.deterministic`. Thus deterministic dynamics sit inside the kernel framework as a special case.

This connection provides a useful bridge to earlier chapters. A measurable map pushes a measure forward by `Measure.map`. Binding the source measure with the deterministic kernel gives the same result, expressed in kernel notation. Therefore, if a proof uses both deterministic and random transitions, the kernel interface can put them into a common compositional language.

Do not confuse a deterministic kernel with the Dirac measure at one fixed point. The former varies with the current state through `f`; the latter is a constant kernel. The distinction appears in the measurability and composition equations.

## 3. One-step evolution of a law

Let `μ` be an initial measure on `α` and `κ` a kernel from `α` to `β`. Binding `μ` with `κ` forms the measure on next states by averaging the transition measures:

\[
  (\kappa\circ_m\mu)(s)
  = \int \kappa(a)(s)\,d\mu(a),
\]

for measurable `s`. In Lean the notation is `κ ∘ₘ μ`; it corresponds to `Measure.bind μ κ`. If `κ` is a Markov kernel and `μ` is a probability measure, the evolved measure is again a probability measure.

This operation handles the law of the next state without choosing a sample space or constructing individual random outcomes. It is therefore particularly effective for distribution-level arguments. If the theorem concerns a specific path, use a process model; if it concerns only the state law, kernel binding often avoids unnecessary path-space machinery.

The integration theorem for a bound function has the same shape: first integrate the function against `κ a`, then average the resulting value over `μ`. For nonnegative functions, the extended nonnegative integral interface is especially robust because it permits infinite values and uses Tonelli-style interchange results.

This gives two complementary views of a transition. In the forward view, the kernel pushes a state distribution to a new distribution. In the backward view, it sends a test function `g` on next states to its expected value after one transition, as a function of the current state. The identity relating the two is

\[
  \int g\,d(\kappa\circ_m\mu)
  =\int\left(\int g(b)\,d\kappa(a)(b)\right)d\mu(a),
\]

when the integrability hypotheses permit ordinary integrals; for nonnegative `g`, the corresponding statement uses `lintegral`. Choosing between the forward measure and backward test-function view is a proof-design decision. Use the forward view for laws and invariance, and the backward view for expected rewards, harmonic functions, or one-step conditional expectations.

The measurability of the backward average is not automatic from pointwise integrability alone. It is supplied by the kernel integration API under its stated measurability conditions. This is one reason a kernel is more than a family of probability measures: the measurable dependence theorem is part of the abstraction.

## 4. Composing transitions

Suppose `κ : Kernel α β` is a first transition and `η : Kernel β γ` is a second. Their composition `η ∘ₖ κ` is a kernel from `α` to `γ`:

\[
  (\eta\circ_k\kappa)(a)(t)
  =\int \eta(b)(t)\,d\kappa(a)(b).
\]

Read the notation from right to left: apply `κ` first, then `η`. The composition theorem `lintegral_comp` expresses integration against the composite as nested integration. Kernel composition is associative, and the Markov-kernel property is preserved by composition.

```text
state in α ──κ──▶ intermediate state in β ──η──▶ state in γ
                   
composite transition: η ∘ₖ κ
```

When `α = β = γ`, a Markov kernel can be composed with itself. Kernel powers model repeated steps. The Chapman–Kolmogorov law says that an `m+n` step transition is obtained by composing the `n`-step transition with the `m`-step transition, with the precise orientation determined by the right-to-left composition convention. Mathlib exposes the integral form through results such as `pow_add_apply_eq_lintegral`.

This is why composition orientation should be checked before simplifying. A common proof error is to write `κ ∘ₖ η` when the types happen to be the same, so elaboration does not reveal the reversed order. Annotate the intermediate state type or inspect the iterated-integral formula.

## 5. Worked example: a two-state chain

Take state space `{0,1}`. From state `0`, transition to `1` with probability `p` and stay at `0` with probability `1-p`. From state `1`, transition to `0` with probability `q` and stay at `1` with probability `1-q`, where `p,q ∈ [0,1]`.

If the current law assigns mass `x₀` to `0` and `x₁` to `1`, the next law is

\[
  (x_0,x_1)\longmapsto
  \big(x_0(1-p)+x_1q,\;x_0p+x_1(1-q)\big).
\]

This is multiplication by the transition matrix

\[
  P=\begin{pmatrix}1-p&p\\q&1-q\end{pmatrix},
\]

viewed as a Markov kernel on a finite measurable space. A stationary distribution solves `πP=π`. When `p+q>0`, it is

\[
  \pi_0=\frac{q}{p+q},\qquad \pi_1=\frac{p}{p+q}.
\]

If `p=q=0`, both states are absorbing and every distribution is stationary, so the positive-denominator hypothesis is mathematically necessary for the displayed formula.

In Lean, one may represent the state type as `Fin 2`; finite measurable spaces make every subset measurable. Define the row measures and prove each is a probability measure, then bundle them into a kernel and install `IsMarkovKernel`. The one-step law is a kernel bind. The stationary calculation reduces to checking the two point masses and using field algebra under the nonzero denominator assumption.

The finite matrix is a convenient calculation model, but the kernel representation is more general. It supports the same composition and measure-evolution interface when the state space is countable or continuous and the transition probabilities are described by measures rather than a finite array.

## 6. Worked example: composing two transitions

Use the two-state chain above twice, with transition matrix `P`. The two-step transition matrix is `P²`. Its entry from state `0` to state `1` is the sum over the possible intermediate states:

\[
  P^{(2)}_{01}=(1-p)p+p(1-q).
\]

The first term is the path `0 → 0 → 1`; the second is `0 → 1 → 1`. The kernel composition formula performs exactly this sum by integrating the second transition against the distribution of the intermediate state. In a finite type, that integral reduces to a finite sum, so `simp`, `Finset.sum` lemmas, and ring normalization can finish the algebra after the measure-theoretic composition theorem has rewritten the goal.

For `n` steps, matrix powers and kernel powers follow the same recurrence. The Chapman–Kolmogorov theorem packages the recursive calculation so a proof does not need to enumerate every path of length `n`. On a general state space, the sum becomes an integral over intermediate states; the kernel theorem is the uniform statement covering both cases.

This example illustrates an effective formalization boundary: prove the kernel composition law once, then perform finite-state arithmetic in a separate lemma. Keeping those steps apart makes the model portable to larger finite state spaces and prevents transition-matrix calculations from obscuring the probabilistic construction.

## 7. From transition kernels to the Markov property

For a process `X n` with state space `E` and filtration `ℱ`, the Markov property informally states that the conditional law of `X (n+1)` given all information through time `n` depends on the past only through `X n`. With transition kernel `κ`, one writes, for measurable `s`,

\[
  P(X_{n+1}\in s\mid\mathcal{F}_n)
  =\kappa(X_n)(s)
  \quad\text{almost surely}.
\]

Equivalently, for suitable measurable functions `g`, the conditional expectation of `g (X (n+1))` given `ℱ n` is the kernel average of `g` at `X n`. The event version is useful for transition probabilities; the integral version is often more convenient for expectations.

The formal proof connects several interfaces: `X n` is measurable, `κ` is a Markov kernel, the event or function is measurable, and conditional expectation satisfies the appropriate set-integral characterization. Mathlib's kernel and conditional-expectation APIs provide these components. Depending on the application, the process-level Markov property may be a predicate defined by the development rather than a single bundled object; inspect the current library before choosing a representation.

For a finite state space, conditioning on the full past can be checked by partitioning on histories and verifying that the next-state probabilities depend only on the current state. For general spaces, a kernel is the right reusable witness because it packages measurability in the state and probability normalization in every row.

This formulation also tells you what should be proved when a process is built from a transition rule: show each coordinate is measurable, show the conditional event probability equals the kernel row at the current coordinate, and then use kernel composition for multi-step predictions. If the process is defined by a recursive construction, keep the one-step Markov property as a lemma; later induction can reuse it without unfolding the path construction.

## 8. Stationary measures and invariance

A probability measure `μ` is stationary for a Markov kernel `κ` if one transition leaves it unchanged:

\[
  \kappa\circ_m\mu=\mu.
\]

This equation is an invariant-measure statement. It can be proved by comparing measures on measurable sets or by comparing integrals of nonnegative measurable functions. Once established, associativity and repeated composition show that every finite-step evolution also preserves `μ`.

Stationarity is not the same as a process being samplewise constant. A chain started from a stationary law can move at every step while its one-time marginal distribution remains unchanged. This distribution-level distinction mirrors the earlier difference between equality in law and almost-sure equality of random variables.

For finite spaces, solve the finite linear equations `πP=π` together with nonnegativity and total mass one. For general state spaces, the relevant proof may use an invariant-measure theorem or a direct integration identity. The kernel API keeps the statement uniform across both settings.

## 9. Proof workflow

1. Choose the current-state and next-state measurable spaces.
2. Define a `Kernel α β` and prove measurable dependence on the current state.
3. Add `IsMarkovKernel` when every transition measure has total mass one.
4. Evolve an initial law with `κ ∘ₘ μ`.
5. Compose transitions in the order “later kernel after earlier kernel.”
6. Use the iterated-integral theorem to rewrite composite transition probabilities.
7. For processes, state the Markov property with respect to an explicit filtration and conditional expectation.
8. Separate distributional invariance from pathwise properties.

This organization makes each obligation local. Kernel measurability belongs to the transition model, probability normalization belongs to `IsMarkovKernel`, and any path-space claim belongs to the process and filtration layer.

## 10. Common failure modes

### A family of measures is assumed to be a kernel

The map from state to event probability must be measurable for each measurable event.

### Kernel and Markov-kernel assumptions are conflated

A general kernel need not have probability measures as its values. State `IsMarkovKernel` when total mass one is required.

### Composition order is reversed

`η ∘ₖ κ` applies `κ` first, then `η`. Use the types and nested-integral formula to check the order.

### Kernel binding is confused with pushforward

Pushforward is the deterministic special case. A random kernel averages over a distribution of next states.

### A stationary law is called a constant path

Stationarity preserves marginal distributions, not individual trajectories.

### The kernel is mistaken for a complete path model

A kernel describes transitions. To reason about histories, stopping, or almost-sure path limits, also define a process and filtration or use a path-space construction.

## 11. Exercises

1. State the measurability condition for a kernel `κ : Kernel α β`.
2. Explain the additional property expressed by `IsMarkovKernel κ`.
3. Show that a measurable map induces a deterministic kernel and relate its bind to `Measure.map`.
4. Write the nested-integral identity for `η ∘ₖ κ` and explain its order.
5. Derive the one-step law of the two-state chain from an initial distribution `(x₀,x₁)`.
6. Verify the stationary distribution formula when `p+q>0`.
7. State the process-level Markov property using conditional probabilities of measurable sets.
8. Explain how kernel composition encodes the Chapman–Kolmogorov relation.
9. Distinguish a stationary distribution from an almost-surely constant process.
10. Identify which proof obligations belong to the kernel, which to the initial measure, and which to the sample-path process.

### 11.1 Compiled kernel patterns

The finite-state identity transition has unit row mass at each state, checked by the shared exact model:

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

theorem transitionRowsHaveMassTwoAtZero : rowMass identityKernel zero = 2 :=
  identity_zero_row
theorem transitionRowsHaveMassTwoAtOne : rowMass identityKernel one = 2 :=
  identity_one_row
```

An `IsMarkovKernel` hypothesis means every transition measure is a probability measure, so each row assigns mass one to the whole state space:

```lean
open MeasureTheory ProbabilityTheory

theorem exercise_40_2_markov_kernel_row_mass
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] (a : α) :
    κ a Set.univ = 1 := by
  simp
```

A measurable map induces a deterministic kernel, and evolving a measure through it agrees with the usual pushforward:

```lean
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem exercise_40_3_deterministic_kernel_map
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (μ : Measure α) :
    Kernel.deterministic f hf ∘ₘ μ = Measure.map f μ := by
  exact MeasureTheory.Measure.deterministic_comp_eq_map hf
```

Kernel composition evaluates a measurable target event by integrating its transition probability over the intermediate state:

```lean
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

theorem exercise_40_4_kernel_comp_apply
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ : Kernel α β) (η : Kernel β γ) (a : α) (s : Set γ)
    (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂κ a := by
  exact Kernel.comp_apply' η κ a hs
```

Composing Markov kernels again gives a Markov kernel, and applying a Markov kernel to a probability measure preserves total mass one:

```lean
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem exercise_40_8_markov_kernel_comp
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ : Kernel α β) (η : Kernel β γ)
    [IsMarkovKernel κ] [IsMarkovKernel η] : IsMarkovKernel (η ∘ₖ κ) := by
  infer_instance
```

```lean
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem exercise_40_5_evolve_probability_measure
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (κ ∘ₘ μ) := by
  infer_instance
```

## Summary

A kernel is a measurable state-indexed family of measures; a Markov kernel assigns a probability measure at every state. Binding a measure with a kernel evolves a law, and kernel composition models consecutive transitions. Finite transition matrices are special cases, while the same interfaces handle general measurable state spaces. A full Markov-process proof also needs a process, filtration, and conditional-expectation statement linking the observed process to its transition kernel.

## Further reading

- [Mathlib: Kernel definitions and Markov kernels](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Defs.html)
- [Mathlib: Kernel composition and Chapman–Kolmogorov](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html)
- [Mathlib: Kernel and measure composition notation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/CompNotation.html)
- [Mathlib: Basic kernel operations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Basic.html)
