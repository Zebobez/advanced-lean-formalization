# Chapter 41 — Disintegration and Conditional Kernels

> **Audience.** This chapter assumes familiarity with product measures, kernels, conditional expectation, and standard Borel spaces. It develops conditional distributions as kernels that reconstruct a joint measure from a marginal and a family of conditional laws.

Conditional expectation answers questions about averages given information. A conditional distribution answers the richer question: what is the entire law of one variable when another variable is observed? The formal object is a kernel. For each value of the observation, the kernel gives a measure on the quantity being conditioned, and measurable dependence on the observation makes the family usable as a single mathematical object.

The central theorem is disintegration. A joint measure on `α × Ω` can, under suitable regularity assumptions, be reconstructed by first drawing its `α`-coordinate and then sampling from a conditional kernel on `Ω`. Mathlib records this reconstruction as an equality of measures, which is more robust than trying to define conditional probabilities by ratios at every point.

The main formalization lesson is that conditional laws are usually unique only almost everywhere with respect to the observed marginal. Values over null observations cannot be recovered from the joint distribution. Standard Borel hypotheses provide existence; the disintegration identity provides the right interface for proofs.

Chapter 42 applies this interface to Bayesian updating: the posterior is the conditional kernel obtained by disintegrating the joint prior-likelihood model after swapping the parameter and data coordinates.

## Learning objectives

By the end of the chapter, you should be able to:

- state disintegration of a joint measure using a conditional kernel;
- understand `Measure.IsCondKernel` as a measure-reconstruction property;
- identify the standard Borel assumptions used for existence;
- reason about uniqueness almost everywhere and null observation values;
- use integral identities to move between joint and conditional calculations;
- distinguish a conditional kernel from pointwise conditional-probability ratios.

## 1. Joint measures and observed marginals

Let `ρ` be a finite measure on `α × Ω`. Think of a point `(a, ω)` as an observation together with a latent or unobserved value. The first marginal `ρ.fst` describes the distribution of the observation `a`; the joint measure retains the dependence between the two coordinates.

A conditional kernel `ρCond : Kernel α Ω` assigns to each `a` a measure on `Ω`. Disintegration asks for this family to satisfy

\[
  \rho = \rho.\mathrm{fst}\otimes_m \rhoCond.
\]

The right-hand side first uses the marginal on `α`, then the conditional kernel to extend each observed state into the second coordinate. On rectangles `s × t`, this says

\[
  \rho(s\times t)=\int_s \rhoCond(a)(t)\,d(\rho.\mathrm{fst})(a).
\]

This rectangle formula gives the intuition, while the measure equality is the stronger library interface: it handles every measurable subset of the product without requiring a separate proof for each shape of event.

```text
joint law ρ on α × Ω
       │ marginalize first coordinate
       ▼
observation law ρ.fst on α
       │ sample conditional distribution ρCond a
       ▼
reconstruct joint law: ρ.fst ⊗ₘ ρCond = ρ
```

## 2. The `IsCondKernel` interface

Mathlib defines `Measure.IsCondKernel ρ ρCond` to mean that `ρCond` disintegrates `ρ`. Its central field is the equality

\[
  \rho.\mathrm{fst}.\mathrm{compProd}\;\rhoCond=\rho.
\]

For a kernel whose output is itself a product, the analogous predicate is `Kernel.IsCondKernel`, and the identity uses kernel composition-product. These predicates package a reconstruction theorem rather than a pointwise formula for every conditional event.

This choice is deliberate. Conditional laws are well behaved under integration even when individual observations have zero probability. The disintegration equation captures exactly the information determined by the joint law. It also makes uniqueness statements naturally almost everywhere with respect to the first marginal.

To use the characterization, prove or obtain the `IsCondKernel` instance and apply the disintegration theorem. To establish that a proposed kernel is conditional, it is enough to verify the joint-measure identity. In concrete cases, checking rectangles or a generating π-system can prove that equality; once the measure equality is established, later event and integral calculations use the packaged interface.

## 3. Existence on standard Borel spaces

Not every measurable space admits a regular conditional distribution for every joint measure. Mathlib's general existence theorem uses standard Borel structure on the space whose conditional law is being produced, together with finiteness and the measurability hypotheses in the relevant theorem. A standard Borel space is, informally, a measurable space that can be modeled as the Borel sets of a well-behaved complete separable metric space.

For a finite measure on `α × Ω`, the standard Borel API constructs `ρ.condKernel` when `Ω` carries the required standard Borel structure. For kernels, the existence theorem also includes countability or countable-generation assumptions on the parameter coordinates. Read the exact theorem signature: the measure and kernel versions have related but not identical side conditions.

The construction for real-valued conditional distributions proceeds through conditional cumulative distribution functions and Stieltjes measures. The general standard Borel construction reduces to the real case through measurable embeddings. Users of the API normally need the resulting kernel and its integral properties, not the details of this construction.

The assumptions are mathematical, not bureaucratic. They provide enough structure to make the conditional law vary measurably with the observation. Without that, each observation might have an individually definable conditional measure while the whole family fails to form a kernel.

On finite spaces, it is often simpler to construct the kernel directly from atom ratios and prove the reconstruction identity. On countable spaces, a countable formula may work when the conditional values are constant on measurable atoms. These explicit constructions can bypass a general existence theorem, but they still must prove measurability and handle null marginal atoms. The standard Borel construction is the scalable choice when the state space is not a finite combinatorial object.

## 4. Uniqueness is almost everywhere

If `κ₁` and `κ₂` both disintegrate the same joint measure, they agree almost everywhere with respect to the observed marginal, under the appropriate hypotheses. They need not agree at every observation. A value `a` with `ρ.fst {a}=0` contributes nothing to the reconstruction identity, so the joint law cannot determine the conditional distribution there.

This is the kernel-valued counterpart of the almost-everywhere uniqueness of conditional expectation. The relevant null sets are now in the observation space, and equality is an almost-everywhere equality of kernels. A pointwise equality goal is generally too strong unless a theorem has chosen a specific version or additional assumptions remove the exceptional observations.

When proving two candidates agree, compare their reconstruction identities rather than evaluating them at individual observations. Once both kernels disintegrate the same joint measure, the uniqueness theorem for conditional kernels gives almost-everywhere equality. This is the stable conclusion to carry into later calculations; replacing it with pointwise equality requires an additional choice of versions or a positivity assumption on each observation under study.

On a finite or countable observation space, the issue becomes concrete. If `a` has positive marginal mass, the conditional measure is forced by

\[
  \rhoCond(a)(t)=\frac{\rho(\{a\}\times t)}{\rho.\mathrm{fst}(\{a\})}.
\]

If the denominator is zero, this ratio is undefined and the conditional law is unconstrained by the joint measure. The abstract kernel construction still assigns a value there, but that value belongs to a version and is not uniquely determined by the probability model.

## 5. Worked example: a finite conditional table

Let the observed variable `A` take values `a₀,a₁` and the latent variable `Y` take values `0,1`. Suppose the joint probabilities are

\[
  P(A=a_0,Y=0)=0.30,\quad P(A=a_0,Y=1)=0.20,
\]
\[
  P(A=a_1,Y=0)=0.10,\quad P(A=a_1,Y=1)=0.40.
\]

The observation marginal is `P(A=a₀)=0.50` and `P(A=a₁)=0.50`. The conditional kernel therefore assigns

\[
  \rhoCond(a_0)(\{0\})=0.6,\qquad
  \rhoCond(a_0)(\{1\})=0.4,
\]
\[
  \rhoCond(a_1)(\{0\})=0.2,\qquad
  \rhoCond(a_1)(\{1\})=0.8.
\]

For example, reconstructing the joint probability of `{a₀} × {1}` gives `0.50 × 0.40 = 0.20`, as required. The same check on the other three atoms proves the comp-product equality because every set in the finite product is a union of atoms.

In Lean, use finite types with their discrete measurable structures, define the joint measure by its atom weights, construct the two conditional probability measures, and prove `IsCondKernel` by extensionality on finite sets or atoms. Once the instance is installed, the library disintegration theorem supplies the desired identity without repeating the atom calculation in every later proof.

## 6. Worked example: a deterministic conditional law

Let `g : α → Ω` be measurable, and define the joint law by sampling `a` from a measure `μ` and pairing it with `g a`. The conditional law of the second coordinate given the first is the Dirac measure at `g a`:

\[
  \rhoCond(a)=\delta_{g(a)}.
\]

Indeed, integrating this kernel against the first marginal recovers the pushforward of `μ` under `a ↦ (a,g a)`. The second coordinate is completely determined by the observation, so its conditional distribution is a point mass.

This example is the conditional-kernel analogue of a deterministic transition kernel from Chapter 40. It also provides a useful API check: disintegrating a measure supported on the graph of a measurable function should recover a Dirac conditional law almost everywhere. If a proof instead requires an arbitrary density or a positive-probability denominator, it may be using a more complicated interface than necessary.

## 7. Integral formulas and generalized Fubini

Disintegration converts an integral over the joint space into nested integration. For a nonnegative measurable `h`, the schematic identity is

\[
  \int^- h(a,\omega)\,d\rho(a,\omega)
  =\int^-\left(\int^- h(a,\omega)\,d\rhoCond(a)(\omega)\right)
     d(\rho.\mathrm{fst})(a).
\]

Mathlib provides `lintegral_condKernel` and set-integral variants; Bochner integral versions require integrability. This is generalized Fubini: the inner measure is not a fixed marginal `ν`, but depends measurably on the outer variable through a kernel.

The integral formula is often the most effective proof route. If the goal concerns the conditional expectation of a function of the latent variable, integrate that function against the conditional kernel. If the goal concerns a joint event, express its indicator as a function on the product and apply the set or lintegral disintegration theorem.

Pay attention to the theorem's order of coordinates. A joint measure on `α × Ω` conditions the second coordinate on the first. Swapping coordinates changes the marginal and the conditional kernel's domain. Product-space goals with a `Prod.swap` often indicate that the disintegration should be stated in the opposite orientation.

## 8. Conditional kernels versus conditional expectations

For a measurable function `g : Ω → E`, integrating `g` against the conditional kernel produces a function of the observation:

\[
  a\longmapsto\int g(\omega)\,d\rhoCond(a)(\omega).
\]

Under the appropriate probability model, this is a version of the conditional expectation of `g(Y)` given the observation. The kernel contains more information than the conditional expectation: one can recover conditional probabilities of all measurable events and conditional expectations of many functions from it.

Conversely, conditional expectation of indicators gives conditional probabilities event by event, but a family of such representatives must be assembled with enough measurability and countable consistency to form a kernel. Standard Borel disintegration is the theorem that performs this assembly under suitable assumptions.

Use conditional expectation when the proof needs a particular average. Use a conditional kernel when it needs the whole conditional law, such as a posterior distribution, a conditional simulation rule, or a family of event probabilities indexed by observations.

For random variables `X : Ω₀ → α` and `Y : Ω₀ → Ω`, form their joint law by pushing the source probability forward along `ω ↦ (X ω, Y ω)`. Disintegrating this joint law with respect to its first marginal gives the conditional law of `Y` given `X`. Integrating a measurable function `g` against the resulting kernel and evaluating at `X` yields a version of the conditional expectation of `g ∘ Y` given the σ-algebra generated by `X`, provided the relevant integrability assumptions hold. This derives a scalar conditional-expectation statement from a stronger distribution-valued object.

That derivation is useful when several functions of `Y` appear in one argument. Construct one conditional kernel, then integrate each test function against it. Without the kernel, a proof may have to build and compare a separate conditional-expectation representative for every function.

For measurable sets `A ⊆ α` and `B ⊆ Ω`, the same construction says

\[
  P(X\in A,\;Y\in B)
  =\int_{\{X\in A\}}\rhoCond(X)(B)\,dP.
\]

Thus the measurable function `a ↦ ρCond a B` is a version of the conditional probability of `{Y ∈ B}` given the observed value. This event-level formula is a convenient bridge when a theorem is stated in probability language but the available API is expressed through a kernel. Prove it once from the joint-law identity and then use it for all measurable `A` rather than repeatedly unfolding the product measure.

## 9. Proof workflow

1. Fix the coordinate order of the joint measure and identify which coordinate is conditioned on.
2. Prove finiteness and the standard Borel assumptions required by the construction.
3. Construct or choose the candidate kernel.
4. Establish the `IsCondKernel` reconstruction identity.
5. Use uniqueness only as an almost-everywhere statement with respect to the first marginal.
6. Select a set-integral, lintegral, or Bochner-integral theorem according to the target.
7. In discrete spaces, handle positive-mass observations with ratio formulas and null observations separately.
8. Preserve coordinate swaps explicitly when the joint measure is rearranged.

This order prevents a common mistake: trying to prove pointwise conditional formulas before the kernel and its version have been specified. Start with the reconstruction identity; derive pointwise atom formulas only when the marginal gives a nonzero denominator.

## 10. Common failure modes

### A conditional law is written as a ratio at every point

The denominator may be zero. The reconstruction equation determines values only almost everywhere with respect to the observation marginal.

### A family of measures is assumed measurable

Pointwise probability measures do not automatically form a kernel. Prove measurable dependence or use the standard Borel construction.

### Existence is asserted without regularity assumptions

Disintegration needs hypotheses such as finiteness and standard Borel structure. Match them to the current theorem.

### Kernel equality is expected pointwise

Conditional kernels are generally unique only almost everywhere. Use the marginal measure on the observation space.

### The coordinate orientation is reversed

The first marginal identifies the observed variable; the kernel produces the conditional law of the second. Track swaps before applying the theorem.

### Bochner integrals are used without integrability

For nonnegative measurable functions, use the lintegral theorem. For vector-valued integrals, prove integrability on the relevant measures.

## 11. Exercises

1. State the measure reconstruction equation defining a conditional kernel.
2. Derive the rectangle identity from the comp-product equality.
3. Compute the four conditional probabilities in the finite-table example and verify one joint atom.
4. Explain why the conditional law is not determined at an observation of zero marginal mass.
5. Describe the standard Borel hypothesis used to obtain a regular conditional law.
6. Show that a deterministic measurable relation `Y=g(X)` has Dirac conditional laws.
7. State the disintegration formula for a nonnegative measurable function on a product space.
8. Explain why a conditional kernel provides more information than one conditional expectation.
9. Find `Measure.IsCondKernel` and the theorem that constructs `ρ.condKernel`; identify their assumptions.
10. Give an example where swapping product coordinates changes which conditional kernel is needed.

### Compiled disintegration patterns

The small finite model supplies an executable transition table, while the following examples check the measure-theoretic interfaces used throughout this chapter. In particular, the construction theorem carries standard Borel and finiteness assumptions, the atomic formula requires positive marginal mass, and uniqueness is stated almost everywhere.

```lean
import Book.Models.FiniteTwoState
import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.Probability.Kernel.Disintegration.Unique

open Book.Models.FiniteTwoState

def conditionalTable : Kernel := resetKernel
def observedMarginalAtZero : Nat := conditionalTable zero zero + conditionalTable one zero

theorem conditionalTableCell : conditionalTable zero one = 1 := by decide
theorem observedMarginal : observedMarginalAtZero = 2 := by decide
```

The `IsCondKernel` predicate exposes the reconstruction equation directly. For the canonical `ρ.condKernel`, Mathlib supplies the instance when the conditioned space is standard Borel and nonempty and the joint measure is finite.

```lean
open MeasureTheory ProbabilityTheory

theorem exercise_41_1_disintegration_identity
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (ρ : Measure (α × Ω)) (ρCond : Kernel α Ω)
    [ρ.IsCondKernel ρCond] :
    ρ.fst ⊗ₘ ρCond = ρ := by
  exact ρ.disintegrate ρCond
```

```lean
open MeasureTheory ProbabilityTheory

theorem exercise_41_2_condKernel_reconstruction
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    ρ.fst ⊗ₘ ρ.condKernel = ρ := by
  exact ρ.disintegrate ρ.condKernel
```

On a measurable singleton with positive marginal mass, the conditional event probability is the joint atom mass divided by the marginal atom mass. The hypothesis is essential because a zero-mass observation does not determine the version.

```lean
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem exercise_41_3_condKernel_atom_formula
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [MeasurableSingletonClass α] [StandardBorelSpace Ω] [Nonempty Ω]
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] {a : α}
    (ha : ρ.fst {a} ≠ 0) (s : Set Ω) :
    ρ.condKernel a s = (ρ.fst {a})⁻¹ * ρ ({a} ×ˢ s) := by
  exact Measure.condKernel_apply_of_ne_zero ha s
```

For a nonnegative measurable function, disintegration turns a joint integral into nested integration against the conditional law and observed marginal.

```lean
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem exercise_41_4_lintegral_disintegration
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]
    (f : α × Ω → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ a, ∫⁻ ω, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫⁻ p, f p ∂ρ := by
  exact ρ.lintegral_condKernel hf
```

The canonical conditional kernel of a measure generated by a Markov kernel agrees with that kernel almost everywhere. This form records the version-independent conclusion.

```lean
open MeasureTheory ProbabilityTheory

theorem exercise_41_5_conditional_kernel_ae_unique
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α Ω) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).condKernel =ᵐ[μ] κ := by
  exact ProbabilityTheory.condKernel_compProd μ κ
```

For a measurable deterministic relation, specialize the preceding result to its Dirac transition kernel. Thus the conditional law is the point mass at the observed image, up to the usual almost-everywhere equality.

```lean
open MeasureTheory ProbabilityTheory

theorem exercise_41_6_deterministic_conditional_law
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure α) [IsFiniteMeasure μ] (g : α → Ω) (hg : Measurable g) :
    (μ ⊗ₘ Kernel.deterministic g hg).condKernel =ᵐ[μ]
      Kernel.deterministic g hg := by
  exact ProbabilityTheory.condKernel_compProd μ (Kernel.deterministic g hg)
```

## Summary

A conditional kernel disintegrates a joint measure into its observed marginal and a measurable family of conditional laws. Mathlib records this through `Measure.IsCondKernel` and constructs such kernels under standard Borel and finiteness assumptions. The reconstruction and integral identities are the stable proof interfaces; pointwise conditional formulas are available for positive-mass atoms, while null observations remain version-dependent. Conditional kernels generalize conditional expectations by retaining the full conditional distribution.

## Further reading

- [Mathlib: Conditional kernels and disintegration](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Disintegration/Basic.html)
- [Mathlib: Existence for standard Borel spaces](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Disintegration/StandardBorel.html)
- [Mathlib: Integral formulas for conditional kernels](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Disintegration/Integral.html)
