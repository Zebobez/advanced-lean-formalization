# Chapter 35 — Conditional Expectation and Information

> **Audience.** This chapter assumes familiarity with probability measures, measurable functions, almost-everywhere equality, and Bochner integration. It develops conditional expectation as an interface between information represented by a σ-algebra and integrable random variables.

Conditional expectation is one of the points where measure theory, probability, and functional analysis meet. Its informal meaning is straightforward: given partial information, replace a random variable by the best prediction measurable from that information. Its formal definition is more robust than a pointwise averaging formula. A conditional expectation is characterized by measurability and by agreement of integrals over every event that can be observed with the available information.

This characterization is valuable in Lean because it works on general probability spaces, including ones without an elementary conditional-density formula. It also determines the API shape: the result is unique only almost everywhere, integrability is an explicit input, and measurable sub-σ-algebras are ordered by inclusion. The chapter emphasizes these interfaces and shows how they lead to the tower property, monotonicity, and conditional probabilities.

## Learning objectives

By the end of the chapter, you should be able to:

- represent partial information by a sub-σ-algebra `m ≤ m₀`;
- understand `μ[f | m]` through its measurability and set-integral properties;
- reason with equality almost everywhere rather than equality of chosen representatives;
- use the tower property when one information set is contained in another;
- identify conditional expectations in finite-partition examples;
- distinguish the mathematical domain assumptions from Lean's total fallback definition.

## 1. A σ-algebra as information

Let `Ω` be a sample space with ambient measurable space `m₀`. A sub-σ-algebra is another measurable structure `m` on `Ω` whose measurable sets are all measurable in `m₀`. Mathlib expresses this relation as an order inequality:

\[
  m \leq m₀.
\]

The order has the expected information meaning. If `m₁ ≤ m₂`, every event observable using `m₁` is also observable using `m₂`; therefore `m₂` represents at least as much information. The bottom measurable space carries only the trivial information, and the top one is the ambient measurable space.

A real-valued function is measurable with respect to `m` exactly when its value can be determined from the information represented by `m`, up to the level of measurable structure. This is the formal meaning of “known at time *t*” in a stochastic process, and it is why the same order relation will reappear in the martingale chapter.

```text
                         more information
                               ↑
             m₁  ───────────▶  m₂
              │  m₁ ≤ m₂       │
              └──── events observable under m₁ are observable under m₂

     conditional expectation onto m₂ retains at least as much detail
```

Conditional expectation is defined for a measure `μ`, a sub-σ-algebra `m`, and an integrable function `f`. In the common real-valued setting, the notation is `μ[f | m]`; the underlying definition is `MeasureTheory.condExp m μ f`. In probability notation one often writes `P[X | m]`.

The notation should be read as an operation on a random variable using an information structure, not as a new measure. The output remains a function on `Ω`, but it is measurable with respect to the smaller σ-algebra. Its defining property says that any event in `m` sees the same integral before and after conditioning.

## 2. The defining characterization

For integrable `f`, the conditional expectation `g = μ[f | m]` has two core properties:

1. `g` is strongly measurable with respect to `m`;
2. for each `m`-measurable set `s`,

\[
  \int_{s} g\,d\mu = \int_{s} f\,d\mu.
\]

In Mathlib, the set-integral property is exposed by `setIntegral_condExp`. It is the central theorem for converting the abstract construction into a useful calculation. If the problem asks about the probability of an event, choose the event as `s`. If the goal is to prove two candidate conditional expectations equal, compare their set integrals and use a uniqueness theorem.

The theorem is more general than the discrete formula “average over all outcomes in a fiber.” No fibers need to have positive probability, and no conditional probability kernel needs to be constructed. The σ-algebra can represent arbitrary information, and the underlying probability space need not be finite or countable.

Uniqueness is almost everywhere. If `g` and `h` are both `m`-strongly measurable, integrable, and have the same integral over every `m`-measurable set, then `g =ᵐ[μ] h`. The measure does not distinguish functions that differ only on a null set. Accordingly, the conditional expectation is not in general a canonical pointwise representative; its canonical mathematical value is its almost-everywhere equivalence class.

This is why proof goals often have the shape `μ[f | m] =ᵐ[μ] g`, not `μ[f | m] = g`. If a later theorem consumes equality under an integral, almost-everywhere equality is exactly the right interface. Avoid selecting a pointwise version unless an application genuinely needs one.

The construction has functional-analytic content. For square-integrable functions, conditional expectation can be understood as orthogonal projection onto the subspace of functions measurable with respect to `m`. Mathlib's construction extends this idea to integrable functions: it obtains an L² projection where possible and then uses the continuous L¹ conditional-expectation map. This explains both the averaging interpretation and the stability properties that appear later.

## 3. Assumptions and the total definition

The mathematical theorem is about an integrable function and a valid sub-σ-algebra. In the current API, `condExp` is nevertheless a total Lean definition: it can be applied even when the expected hypotheses are absent. The intended construction uses the relation `m ≤ m₀`, integrability of `f`, and a σ-finiteness condition for the measure trimmed to `m`.

If the sub-σ-algebra condition fails, if the function is not integrable, or if the trimmed measure is not σ-finite, the definition is set to zero. This design makes the operation total at the type level, but it does not mean the resulting zero function is a meaningful conditional expectation in those cases. Keep the assumptions next to the use of the API, and do not mistake successful elaboration for a proof that the mathematical preconditions hold.

The exact typeclass assumptions vary across theorems. The basic construction is stated for real normed vector spaces with the required completeness assumptions supplied where needed. Integrability of the result is available from `integrable_condExp`; measurability is available from `stronglyMeasurable_condExp`. Set-integral and uniqueness results carry the hypotheses needed to use the construction correctly. When an application fails to find a theorem, inspect its assumptions before introducing extra instances or coercions.

In probability applications, the ambient measure is often finite, and its restrictions to sub-σ-algebras inherit convenient finiteness properties. For a general measure, however, σ-finiteness should be made explicit. A proof that quietly relies on a probability instance may not generalize to an arbitrary measure.

## 4. Two extremal information structures

The bottom σ-algebra contains only trivial information. Conditioning on it produces a constant almost everywhere whose value is the global mean. Under a probability measure, this is the familiar identity

\[
  \mathbb{E}[X \mid \{\varnothing,\Omega\}] = \mathbb{E}[X]
  \quad\text{almost surely}.
\]

This gives a useful sanity check for a conditional-expectation proof. If a calculation with the trivial information structure does not reduce to the expectation of `X`, the order or notation for the sub-σ-algebra may have been reversed.

At the other extreme, conditioning on all ambient measurable information changes nothing, provided `f` is already measurable and integrable:

\[
  \mathbb{E}[X \mid m₀] = X
  \quad\text{almost surely}.
\]

The phrase “almost surely” still matters. The library theorem identifies the constructed representative with `f` up to null sets. The measurable function may be modified on a null set without affecting its integrals or its probabilistic meaning.

These cases are useful as base points for calculations. They also explain conditional expectation as an information-sensitive version of averaging: discard information and obtain a coarser, often constant, prediction; retain all information and recover the original variable.

## 5. Worked example: a finite partition

Consider a finite probability space with four equally likely outcomes and a random variable taking values

\[
  f(1)=0,\qquad f(2)=2,\qquad f(3)=4,\qquad f(4)=6.
\]

Suppose the available information distinguishes the blocks `{1,2}` and `{3,4}`, but cannot distinguish outcomes inside a block. The conditional expectation must be constant on each block. The set-integral characterization determines those constants. On the first block, the original integral is proportional to `0 + 2`, so the conditional value is `1`; on the second it is proportional to `4 + 6`, so the conditional value is `5`.

```text
block A = {1, 2}:       (0 + 2) / 2 = 1
block B = {3, 4}:       (4 + 6) / 2 = 5

f:       0   2   4   6
E[f|m]:  1   1   5   5
```

The proof design follows the abstract theorem. First establish that the proposed function is measurable with respect to the partition σ-algebra. Then check the set-integral identity on the measurable atoms; finite unions follow by additivity. Finally, apply uniqueness to conclude almost-everywhere equality with the library conditional expectation.

This is a reusable strategy for finite models. It avoids unfolding the internal construction and scales from two blocks to a finite partition. In code, the exact representation might be a finite sample type, a `Fintype` probability measure, or a sub-σ-algebra generated by a partition. The mathematical proof remains the same: measurability plus matching integrals on generators.

The example also identifies a common misconception. Conditional expectation does not necessarily choose a value that appeared among the original outcomes. The value `1` is an average and is not one of `0` or `2`; what matters is that it is measurable from the coarse information and preserves integrals on observable events.

## 6. Worked example: conditional probability

For an event `A`, its indicator `1_A` is integrable on a probability space. The conditional expectation

\[
  \mathbb{E}[1_A \mid m]
\]

is a version of the conditional probability of `A` given `m`. It is `m`-measurable and takes values between zero and one almost everywhere. For any event `B` observable under `m`,

\[
  \int_B \mathbb{E}[1_A \mid m],dP = P(A\cap B).
\]

The right side follows from the set-integral property and the identity `1_A` integrated over `B` equals the measure of `A ∩ B`. This lets a proof derive conditional-probability statements from the more general conditional-expectation API.

Use the indicator theorem `integral_condExp_indicator` when available for this pattern, and use `condExp_nonneg` or the monotonicity theorem to establish bounds. Avoid building a separate conditional-probability object when the statement only needs this random variable and its event-integral property.

On a finite partition, the conditional probability is the ratio of the mass of `A` inside a block to the mass of that block, whenever the block has positive mass. The abstract definition avoids a division-by-zero branch for null blocks: the value on a null block is irrelevant almost surely. This is one reason the measure-theoretic API is more general than a pointwise quotient formula.

## 7. The tower property

Suppose `m₁ ≤ m₂`: information in `m₁` is contained in the richer information in `m₂`. Conditioning first on `m₂` and then on `m₁` gives the same result as conditioning directly on `m₁`:

\[
  \mathbb{E}\big[\mathbb{E}[X\mid m₂]\mid m₁\big]
  = \mathbb{E}[X\mid m₁]
  \quad\text{almost surely}.
\]

Mathlib exposes this through `condExp_condExp_of_le`. The order hypothesis is part of the mathematics, not a technical artifact. If the purported outer conditioning structure contains more information than the inner one, the formula is generally false.

```text
X ── condition on m₂ ──▶ E[X | m₂]
                           │
                           │ condition on coarser m₁
                           ▼
                       E[X | m₁]

Direct route:  X ── condition on m₁ ──▶ E[X | m₁]
```

The proof strategy is to identify the result of the second conditioning by the characterization. It is measurable with respect to `m₁`; its integral over every `m₁`-measurable set agrees with the integral of `X`; uniqueness gives the almost-everywhere conclusion. This proof explains why the tower property is such a stable library theorem: it is a direct consequence of the defining interface.

In applications, the tower property supports iterated conditioning and dynamic programming. It also helps reorganize a proof to condition on the information most naturally associated with each stage, then simplify adjacent stages using the order relation.

## 8. Positivity, order, and linearity

Conditional expectation respects order. If `f ≤ g` almost everywhere, then their conditional expectations have the same order almost everywhere. In particular, nonnegative functions have nonnegative conditional expectations. The corresponding theorems include `condExp_mono` and `condExp_nonneg`.

The linear structure is captured by the L¹ operator `condExpL1CLM`, a continuous linear map on integrable-function classes. This is often the best conceptual level for arguments involving sums or scalar multiples: the operation is linear on L¹ equivalence classes, while the function-level notation presents a representative for pointwise measure-theoretic work.

For real-valued integrable functions, the basic algebraic laws allow conditional expectation to pass through finite sums and constant scalar multiples. The norm and positivity properties provide stability. When using a theorem directly on functions, remember that the output comparison may be almost everywhere even if the corresponding L¹ statement is an equality of equivalence classes.

For vector-valued functions, the Bochner-integral formulation remains available in suitable complete real normed spaces. The value is still characterized by measurability and set integrals. Scalar order statements such as nonnegativity are inherently real-valued; they do not generalize to arbitrary vector spaces without an appropriate order structure.

## 9. A proof workflow

1. Identify the ambient measurable space `m₀` and the information σ-algebra `m`.
2. Prove or obtain the order relation `m ≤ m₀`.
3. Establish integrability of the random variable before using the characterization.
4. Use `stronglyMeasurable_condExp` and `integrable_condExp` for the output properties.
5. For event calculations, apply `setIntegral_condExp` to an `m`-measurable set.
6. For uniqueness, show measurability and compare set integrals, then conclude almost-everywhere equality.
7. For nested information, check the order carefully before applying the tower theorem.
8. For conditional probabilities, start with the indicator of the event and use nonnegativity and monotonicity.

When a proof is algebraic, use the conditional-expectation linearity interface rather than expanding integrals repeatedly. When a proof is probabilistic, choose the event set first; that choice usually determines the appropriate set-integral theorem and makes the required measurability assumption explicit.

## 10. Common failure modes

### The information order is reversed

`m₁ ≤ m₂` means that `m₁` has fewer measurable events. Write down this interpretation before applying the tower property.

### Pointwise equality is demanded

Conditional expectations are unique almost everywhere. Use `=ᵐ[μ]` unless the problem explicitly fixes a representative.

### A theorem elaborates without the intended assumptions

The total definition can return zero outside its mathematical domain. Prove the sub-σ-algebra, integrability, and σ-finiteness assumptions needed for the theorem you intend to use.

### Measurability is confused with integrability

Strong measurability says the output depends only on the specified information. Integrability is a separate property and is required for the integral characterization.

### A set integral is applied to a nonmeasurable event

The test set must be measurable for the conditioning σ-algebra. An event measurable only in the ambient space may not be observable from the given information.

### A finite conditional-probability quotient is used on a null block

The ratio formula requires a positive denominator. The abstract almost-everywhere formulation does not: values on null blocks do not affect the conditional expectation class.

## 11. Exercises

1. State the two properties that characterize `μ[f | m]` for integrable `f`.
2. Explain why uniqueness gives almost-everywhere equality rather than pointwise equality.
3. On a uniform finite space with values `1, 3, 2, 8`, condition on the partition `{1,2}` and `{3,4}`. Compute the conditional expectation and verify the integral condition on each block.
4. Derive the conditional-probability integral identity from the indicator characterization.
5. State the tower property for `m₁ ≤ m₂` and explain the order relation in words.
6. Show how conditional expectation onto the bottom information reduces to a constant mean under a probability measure.
7. Find the library result that identifies conditional expectation of an already measurable integrable function with that function almost everywhere.
8. Explain why a nonnegative function has a nonnegative conditional expectation and identify the corresponding Mathlib theorem.
9. Describe the role of `condExpL1CLM` and why its domain is an L¹ space rather than arbitrary functions.
10. Give an example where two representatives differ at a null point but represent the same conditional expectation.

## Summary

Conditional expectation is the integrable function measurable with respect to a chosen sub-σ-algebra whose set integrals agree with those of the original function on every observable event. The defining characterization yields uniqueness almost everywhere, the tower property, conditional probabilities, positivity, and linearity. In Lean, make information order, integrability, measurability, and almost-everywhere equality explicit. Remember that `condExp` is total by definition, while its intended mathematical properties require the assumptions documented by the corresponding theorems.

## Further reading

- [Mathlib: Conditional expectation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.html)
- [Mathlib: Conditional Lebesgue expectation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConditionalLExpectation.html)
- Chapters 31–34 for measurability, integration, product measures, and probability measures.
