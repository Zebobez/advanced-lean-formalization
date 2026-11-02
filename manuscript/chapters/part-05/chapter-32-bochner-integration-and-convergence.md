# Chapter 32 — Bochner Integration and Convergence Theorems

> **Audience.** This chapter assumes familiarity with measurable functions, normed vector spaces, filters, and convergence of sequences. It develops the Bochner integral API, the distinction between real-valued and extended-nonnegative integrals, and the proof structure of dominated convergence.

Mathlib uses the Bochner integral as its general integration interface. Its domain can be any measure space, and its codomain can be a complete normed real vector space. Ordinary real-valued Lebesgue integration is one important instance. The generality means theorem statements carry several assumptions, but those assumptions have a stable mathematical interpretation: measurability up to null sets, integrability of the norm, and completeness of the target.

The key proof-design choice is whether a result concerns the integral of a single function or convergence of a family of integrals. Basic algebraic properties use `Integrable` hypotheses; almost-everywhere equality gives invariance; convergence theorems require a uniform bound or another condition that controls mass. This chapter shows how to make those dependencies explicit instead of unfolding the integral.

## Learning objectives

By the end of the chapter, you should be able to:

- state the function-space assumptions for a Bochner integral;
- use integrability hypotheses to apply linearity and norm bounds;
- replace a function by an almost-everywhere equal representative;
- distinguish `∫` from the extended nonnegative `∫⁻`;
- apply dominated convergence by matching its hypotheses to the theorem interface.

## 1. The Bochner integral and its target

For a measure `μ` on `α` and a function `f : α → E`, the notation

```text
∫ x, f x ∂μ
```

denotes the Bochner integral. The target `E` is a normed additive commutative group and a real normed space; completeness is used in the construction of the integral. This extends scalar Lebesgue integration to vector-valued functions, including maps into Banach spaces.

The notation is total: Mathlib defines the integral to be zero when the function is not integrable. This convention avoids carrying a proof of integrability in the result type, but it does not make integral identities true without hypotheses. For example, linearity theorems generally require integrability of the functions involved. If an integrability hypothesis is missing, prove it or use a theorem that directly accommodates the weaker conditions.

The condition `Integrable f μ` combines almost-everywhere strong measurability with finite integral of the norm. This matches the construction through the space `L¹`: integrable functions are represented by equivalence classes modulo almost-everywhere equality, and the integral is defined on that class. The public `integral` API lets most proofs avoid manipulating those equivalence classes directly.

The `L¹` space makes this quotient viewpoint explicit. Its elements are equivalence classes of functions with finite first moment, equipped with a norm built from integrating the pointwise norm. A proof that an operation is well-defined on `L¹` must show that it respects almost-everywhere equality and preserves integrability. The ordinary integral then acts as a continuous linear map from `L¹` to the target Banach space. This perspective explains both `integral_congr_ae` and the norm bound in the next sections.

Do not assume every measure is σ-finite. Many basic integral theorems work without that assumption, while approximation and decomposition results may require σ-finiteness. If a theorem asks for `[SigmaFinite μ]`, the condition is likely used to cover the space by countably many finite-measure pieces, not just for technical convenience.

## 2. Linearity and algebraic properties

When `f` and `g` are integrable, integration preserves addition. It also preserves negation and subtraction, and commutes with scalar multiplication. A standard example is:

```lean
open MeasureTheory

example {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f g : α → E) (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = (∫ x, f x ∂μ) + ∫ x, g x ∂μ := by
  exact integral_add hf hg
```

The parentheses make the intended sum of the two integrals clear. In larger proofs, first name the integrability facts, then apply the algebraic theorem. This keeps the calculation independent of how integrability itself was established.

For real-valued nonnegative functions, there is also the `lintegral`, written `∫⁻`. It takes values in `ℝ≥0∞` and can represent infinite integrals without a separate integrability assumption. The Bochner integral `∫` takes values in a vector space and is designed for integrable functions. For a nonnegative real function that is integrable, the two notions are related by a conversion theorem. Keep them separate until the hypotheses justify that conversion.

## 3. Almost-everywhere invariance

The Bochner integral depends only on the almost-everywhere equivalence class of a function. If `f =ᵐ[μ] g`, then their integrals agree:

```lean
open MeasureTheory

example {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : α → E} (h : f =ᵐ[μ] g) :
    ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  exact integral_congr_ae h
```

This theorem is useful well beyond the final integral step. If a function has a convenient measurable representative that agrees with the original almost everywhere, replace it before proving integrability or applying a convergence theorem. The `ae` filter composes the exceptional sets without requiring a pointwise equality proof.

The same principle governs many hypotheses in analysis: limits may hold almost everywhere, order inequalities may hold almost everywhere, and measurability may be specified up to null sets. Use the `ae` form when the theorem is insensitive to null modifications. Do not strengthen an almost-everywhere hypothesis to a pointwise one unless the measure or the functions provide a reason.

An effective proof often has a short representative-selection phase. First find a measurable or strongly measurable function `g` with `f =ᵐ[μ] g`. Use the theorem that changes representatives to establish the property for `g`; then transfer the conclusion back to `f` through an almost-everywhere congruence lemma. This isolates pointwise pathologies in a null set and keeps the main analytic argument focused on the regular representative.

## 4. Norm estimates and order

The norm of an integral is bounded by the integral of the norm:

\[
  \left\|\int f\,d\mu\right\| \leq \int \|f\|\,d\mu.
\]

This estimate connects vector-valued integration to nonnegative scalar integration. It is often the right final step in a convergence proof: bound the norm of a difference of integrals by the integral of the norm of a difference, then show that scalar quantity tends to zero.

For real-valued functions, almost-everywhere order inequalities pass through the integral. If `f ≤ᵐ[μ] g` and the relevant functions are integrable, then the integral of `f` is at most the integral of `g`. The almost-everywhere form is the natural one because changing a function on a null set does not change its integral.

Keep signed and nonnegative estimates distinct. For a real-valued function, the norm is nonnegative even when the function itself changes sign. A theorem about `∫⁻` requires values in `ℝ≥0∞`; use the norm or positive part when converting a signed estimate to that setting.

## 5. Integration over a set

The integral over a measurable set `s` can be written using the restriction of the measure to `s`, or with the set-integral notation provided by Mathlib. Conceptually, these are related by multiplying the function by the indicator of `s`. The set version often makes a proof's domain restriction more visible, while the restricted-measure version can compose naturally with other measure constructions.

When moving between the two forms, check that `s` is measurable or at least null-measurable under the relevant measure. The measure of the intersection and the behavior of the indicator are simplified using that hypothesis. A proof should not silently replace a measurable set by an arbitrary subset when applying an additivity theorem.

Partition arguments use disjoint measurable sets. Countable additivity of the measure and additivity of the integral are then aligned: the domain is partitioned, and each piece contributes one term. For infinite sums, additional summability or integrability assumptions are required before interchanging the sum and integral.

## 6. Dominated convergence

The dominated convergence theorem is a main interface for moving a limit through an integral. For a sequence `F n`, its standard hypotheses say:

1. each `F n` is almost-everywhere strongly measurable;
2. a single real-valued bound is integrable;
3. the norm of each `F n` is bounded by that function almost everywhere;
4. `F n x` converges to `f x` for almost every `x`.

The conclusion is that the integrals of `F n` converge to the integral of `f`. Mathlib packages this as `MeasureTheory.tendsto_integral_of_dominated_convergence`. The bound is uniform in `n`; proving a separate bound for every term is not enough unless those bounds can be dominated by one integrable function.

The proof-state diagram is:

```text
measurability + one integrable bound + a.e. pointwise convergence
                              │
                              ▼
          convergence of the integral sequence
```

The theorem does not ask for a separate integrability proof of the limit in its main interface; the domination and convergence hypotheses provide the needed control. This is a useful example of a library theorem packaging a nontrivial analytic argument. When applying it, align the index type, bound, measure, and target normed space first. Then supply the four hypotheses in the order indicated by the theorem signature.

For a filter-indexed family rather than a sequence, Mathlib provides a filter form of dominated convergence. That result requires the index filter to be countably generated. This connects with Chapter 24: the convergence mode belongs in the filter argument, while the measure's `ae` filter records the exceptional set in the domain.

When the end goal is a numerical limit, it can help to phrase the target as `Tendsto` from `atTop` to a neighborhood filter. This matches the filter interface and composes with other limit statements. If the goal instead asks for an explicit error bound, dominated convergence may hide too much quantitative information; use an integral norm estimate and bound the difference directly. The qualitative theorem establishes convergence but does not by itself provide a rate.

## 7. Monotone convergence and Fatou-style arguments

For nonnegative functions, monotone convergence and Fatou's lemma are commonly expressed using the `lintegral`. The codomain `ℝ≥0∞` handles unbounded integrals, and monotone sequences can converge to an infinite value. This avoids forcing a finite real answer before the mathematics supplies one.

Choose monotone convergence when a sequence increases pointwise to a limit and the goal is to identify the limit of the integrals. Choose Fatou's lemma when only a lower bound on the integral of a limit inferior is needed. Dominated convergence is stronger in a different direction: it handles signed or vector-valued functions under an integrable norm bound and almost-everywhere convergence.

These theorems are not interchangeable. A proof should match the actual hypotheses: monotonicity, nonnegativity, or domination. If the functions are real-valued and signed, pass to a nonnegative expression such as the norm before invoking a `lintegral` result.

## 8. Continuous linear maps commute with integration

If `L : E →L[ℝ] F` is a continuous linear map and `f` is integrable, then applying `L` to the integral agrees with integrating `L ∘ f`. This is the integration counterpart of a homomorphism preserving algebraic operations. It is useful for coordinate projections, bounded linear functionals, and maps between Banach spaces.

The continuity requirement controls the norm and therefore preserves integrability. A merely linear map need not be bounded in infinite-dimensional spaces, so it cannot be assumed to commute with the integral. Use the continuous-linear-map API and let the theorem carry that analytic condition.

For finite-dimensional vector-valued integrals, coordinatewise reasoning can sometimes reduce the goal to scalar integrals. The continuous linear map theorem is the reusable way to make that reduction; avoid reconstructing the coordinate sum by hand unless the coordinates themselves are part of the result.

This theorem is also useful for duality arguments. If every continuous linear functional takes the same value on two integrals, a separating-duality theorem can sometimes show that the vector integrals themselves are equal. The analytic part is handled by commuting each functional with integration; the final identification uses the normed-space structure. Keeping these stages separate makes abstract vector-valued proofs easier to read.

## 9. A proof workflow

1. Determine whether the target is scalar, `ℝ≥0∞`-valued, or a general normed space.
2. Establish `AEStronglyMeasurable` and integrability where the chosen theorem requires them.
3. Use `Integrable` hypotheses for linearity; use almost-everywhere equality for representative changes.
4. For inequalities, choose between order properties of `∫` and nonnegative results for `∫⁻`.
5. For a limit of integrals, identify the convergence theorem and prove its uniform control hypothesis explicitly.
6. Use `norm_integral_le_integral_norm` or a continuous linear map theorem to reduce vector-valued goals.
7. Keep set restrictions and measure transformations visible in the notation.

This workflow separates analytic assumptions from algebraic calculations. The integral notation is deliberately concise, but the proof should still reveal why the function is integrable and why a limiting operation is valid.

## 10. Common failure modes

### Linearity is used without integrability

Prove `Integrable f μ` and `Integrable g μ` first. The total definition of the integral does not make every algebraic law unconditional.

### Pointwise equality is required where almost-everywhere equality suffices

Use `integral_congr_ae` and the `ae` filter to avoid constructing an unnecessary pointwise proof.

### A signed integral is treated as an `ℝ≥0∞` integral

Use `lintegral` for nonnegative extended-valued functions; use `integral` for vector-valued or signed functions.

### A family has bounds but no common integrable dominator

Dominated convergence needs one bound valid almost everywhere for every index. Prove this uniform statement before applying the theorem.

### The limit is moved through the integral without a convergence theorem

Pointwise convergence alone is insufficient. Supply domination, monotonicity, or another theorem's hypotheses.

### A linear map is pushed through the integral without continuity

Use a continuous linear map. Boundedness is part of the analytic argument.

## 11. Exercises

1. Prove additivity of the Bochner integral from `integral_add`, listing the required hypotheses.
2. Replace an integrand by an almost-everywhere equal function using `integral_congr_ae`.
3. State the norm estimate for a Bochner integral and explain how it can prove convergence of integrals.
4. Compare `∫` and `∫⁻`, including their codomains and typical hypotheses.
5. Apply dominated convergence to a sequence and identify the role of the common integrable bound.
6. Explain why pointwise convergence does not, by itself, justify passing a limit through an integral.
7. Use a continuous linear functional to reduce a vector-valued integral identity to a scalar-valued one.
8. Decide whether a proposed argument should use monotone convergence, Fatou's lemma, or dominated convergence, and list the needed conditions.

## Summary

The Bochner integral handles functions into complete normed real vector spaces. Integrability combines almost-everywhere strong measurability with finite integral of the norm; the integral is defined as zero outside that class, but algebraic laws still need their hypotheses. The integral is invariant under almost-everywhere equality, satisfies norm and order bounds, and commutes with continuous linear maps. Use `∫⁻` for nonnegative extended-valued integration. To pass a limit through an integral, match the hypotheses of dominated, monotone, or Fatou convergence rather than relying on pointwise convergence alone.

## Further reading

- [Mathlib: Bochner integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html)
- [Mathlib: Dominated convergence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/DominatedConvergence.html)
- [Mathlib: Strongly measurable functions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.html)
- [Mathematics in Lean: Integration and measure theory](https://leanprover-community.github.io/mathematics_in_lean/)
