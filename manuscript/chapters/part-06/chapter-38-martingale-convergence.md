# Chapter 38 — Martingale Convergence and Uniform Integrability

> **Audience.** This chapter assumes familiarity with martingales, conditional expectation, Bochner integration, and convergence almost everywhere. It develops the boundedness conditions that yield almost-sure or L¹ convergence of a submartingale.

Martingale identities constrain conditional means, but they do not by themselves say that sample paths converge. A sequence can continue to oscillate while preserving its expectation. Convergence theorems add an analytic control condition—typically boundedness in L¹ for almost-everywhere convergence, or uniform integrability for convergence in L¹.

The formalization challenge is to keep the mode of convergence and the bound aligned. Almost-everywhere convergence is a statement about sample paths outside a null set. L¹ convergence is convergence in a norm and therefore controls average error. Uniform integrability is the bridge that upgrades almost-sure behavior to convergence of integrals. Mathlib's martingale convergence interface states these conclusions with the filtration, adaptedness, and integrability hypotheses visible.

This chapter presents the proof architecture behind those results, including the upcrossing argument, the terminal information σ-algebra, and the conditional-expectation martingale. It also explains how to choose the right theorem for a formal goal rather than treating “martingale convergence” as one undifferentiated fact.

## Learning objectives

By the end of the chapter, you should be able to:

- distinguish almost-everywhere convergence from L¹ convergence;
- state L¹ boundedness and explain its role in submartingale convergence;
- understand why uniform integrability is needed for norm convergence;
- describe the upcrossing strategy behind the a.e. theorem;
- identify the limiting filtration `ℱ∞`;
- apply the convergence interface to conditional-expectation martingales.

## 1. Two different convergence conclusions

For a sequence of random variables `f n`, almost-everywhere convergence to `g` means that for almost every outcome `ω`, the real sequence `f n ω` converges to `g ω`. In Lean, this is naturally expressed using `Tendsto` and an almost-everywhere filter. It gives pathwise convergence on a set of full measure but does not, on its own, bound the expected distance from `f n` to `g`.

Convergence in L¹ instead says that the L¹ norm of the difference tends to zero:

\[
  \int \lVert f_n-g\rVert\,d\mu \longrightarrow 0.
\]

This implies convergence in probability under standard measure assumptions, but the key point for formal proof design is that it is a norm statement. An almost-everywhere limit theorem should not be used as if it returned L¹ convergence.

```text
almost-everywhere convergence: paths converge outside a null set
uniform integrability:         large tails are uniformly controlled
                                │
                                ▼
L¹ convergence:                 mean norm error tends to zero
```

The theorem choice follows from the target. If the goal is a pointwise limit process almost everywhere, use the a.e. convergence result and prove L¹ boundedness. If the goal is convergence of expectations or integrals of differences, establish uniform integrability and use the L¹ result.

## 2. L¹ boundedness

A process is L¹-bounded when the L¹ norms of its values are uniformly bounded:

\[
  \sup_n \int |f_n|\,d\mu < \infty.
\]

This condition prevents the expected magnitude from growing without limit. For a real submartingale, L¹ boundedness is enough for almost-everywhere convergence to an integrable limit. Mathlib's theorem `Submartingale.ae_tendsto_limitProcess` formalizes this result for a strongly adapted L¹-bounded submartingale.

When translating a problem into the API, look for a reusable bound on `∫ ‖f n‖`. A bound on the pointwise values is stronger than necessary and may be unavailable. A bound only on `∫ f n` is not enough for a signed process because large positive and negative values can cancel; use the L¹ norm or absolute value.

For nonnegative submartingales, expectation bounds directly control the L¹ norm. For general real-valued processes, an argument may need a lower bound, a decomposition, or an explicit norm estimate. Do not assume the submartingale inequality alone bounds `∫ |f n|` without checking the sign conditions.

## 3. Upcrossings: why paths converge

The standard proof of a.e. submartingale convergence uses upcrossings. Fix rational numbers `a < b`. An upcrossing of `[a,b]` occurs when a path moves from at or below `a` to at or above `b`. Each completed upcrossing records a genuine oscillation of size at least `b-a`.

If a real sequence fails to converge while remaining bounded, then there exist rational `a < b` that it crosses upward infinitely many times. The submartingale upcrossing inequality bounds the expected number of such crossings in terms of the process's integrability. Under the L¹ bound, this expected count is finite, so the number of upcrossings is finite almost surely for each rational pair. There are only countably many rational pairs, so almost every path has only finitely many upcrossings for all of them.

The L¹ bound also controls pathwise limsup: Fatou's lemma gives an integrable bound on `limsup |f n|`, hence this limsup is finite almost everywhere. A real sequence with finite limsup in absolute value and finitely many upcrossings of every rational interval must converge. This yields the almost-everywhere limit.

```text
path:       •──╲   ╱──•──╲   ╱──•
level b:  ──────╱───╲─────────────
level a:  ────╱───────╲───────────
                 ↑ one completed upcrossing
```

Lean's library theorem hides the technical construction of the upcrossing count, but knowing the proof outline helps identify missing assumptions. If a convergence application fails, ask whether the theorem needs a real-valued submartingale, strong adaptation, L¹ boundedness, or a specific index structure.

## 4. The almost-everywhere convergence theorem

For a strongly adapted L¹-bounded submartingale `f`, the sequence converges almost everywhere to an integrable function. Because each `f n` is measurable with respect to `ℱ n`, the limit is measurable with respect to the supremum filtration

\[
  \mathcal{F}_\infty = \bigvee_{n\in\mathbb{N}}\mathcal{F}_n.
\]

This is the σ-algebra generated by all information revealed at finite times. Mathlib expresses the limit through a limit-process construction, and `ae_tendsto_limitProcess` gives the almost-everywhere convergence statement. The limit's integrability and measurability are available through companion results.

The conclusion is carefully calibrated: it provides an integrable limit and almost-everywhere convergence. It does not promise L¹ convergence. That stronger result needs uniform integrability, treated next.

When applying the theorem, package the uniform L¹ bound in the exact predicate expected by Mathlib. A hand-written statement that every integral is bounded may be mathematically equivalent but not syntactically identical to the library's `L1Bounded` interface. Use the definition or constructor theorem to bridge the forms once, then reuse it.

## 5. Uniform integrability

Uniform integrability controls tails uniformly across the whole family. Informally, for large thresholds `K`, the expected contribution from values larger than `K` is small uniformly in `n`. It is stronger than an L¹ norm bound and prevents a small amount of mass from carrying an arbitrarily large value farther and farther out in the sequence.

For example, random variables can converge to zero almost surely while retaining expectation one by placing increasingly large values on increasingly rare events. Their sample paths eventually see zero, but their expectations do not converge to the expectation of the limit. Uniform integrability rules out this escaping-tail phenomenon.

Mathlib provides a measure-theory interface for uniform integrability and probability-specific variants. The exact definition uses a tail-control formulation adapted to the measure assumptions. Prefer the library predicate and its equivalence theorems over manually unfolding a textbook definition; this gives convergence theorems the form they expect.

Uniform integrability implies L¹ boundedness under the relevant probability conditions, but the converse is false in general. Therefore an L¹ bound is sufficient for the almost-everywhere submartingale theorem but not a replacement for uniform integrability in the L¹ convergence theorem.

## 6. L¹ martingale convergence

An L¹-bounded submartingale converges almost everywhere. If the submartingale is uniformly integrable, it also converges in L¹. Mathlib's convergence file includes this stronger theorem and the martingale specialization.

For a uniformly integrable martingale with limit `g`, the values are recovered as conditional expectations of the limit:

\[
  f_n = \mathbb{E}[g\mid\mathcal{F}_n]
  \quad\text{almost surely}.
\]

Conversely, if `g` is integrable and measurable with respect to `ℱ∞`, then the process `n ↦ E[g | ℱ n]` is a uniformly integrable martingale and converges to `g` almost everywhere and in L¹. This links convergence back to the conditional-expectation construction from Chapter 35.

The terminal measurability condition matters. If `g` depends on information outside `ℱ∞`, the sequence of conditional expectations need not recover it in the limit. The sigma-algebra generated by the filtration describes exactly what can be learned from the process over time.

## 7. Worked example: refining conditional predictions

Let `g` be integrable and measurable with respect to `ℱ∞`. Define

\[
  M_n = \mathbb{E}[g\mid\mathcal{F}_n].
\]

Chapter 36 establishes that `M` is a martingale. The L¹ convergence theorem adds two conclusions: `M_n` converges almost everywhere to `g`, and `M_n` converges to `g` in L¹. In statistical language, each `M_n` is the prediction using information available at time `n`; as the filtration reveals all the information determining `g`, the predictions recover `g`.

The formal proof is modular. First use the conditional-expectation martingale theorem. Next establish uniform integrability of the family, using the theorem for conditional expectations of a fixed integrable function. Finally apply the L¹ martingale convergence result and identify the limit using terminal measurability and uniqueness of conditional expectation.

This example is particularly useful as a proof template because the family is not bounded pointwise in general. The right control is uniform integrability, not an arbitrary supremum bound on every sample path.

## 8. Worked example: a nonnegative martingale

Suppose `M` is a nonnegative martingale and its initial expectation is finite. Since martingale expectations are constant, each `M n` has the same expectation. Nonnegativity then identifies the L¹ norm with the expectation, so the process is L¹-bounded. The almost-everywhere convergence theorem yields a finite limit almost surely.

This conclusion does not by itself imply L¹ convergence. A nonnegative martingale can converge almost surely while failing to be uniformly integrable; mass can escape into increasingly rare large values. To obtain L¹ convergence, prove uniform integrability or a sufficient condition such as a uniform Lᵖ bound for some `p > 1`, with the appropriate measure assumptions.

In Lean, make nonnegativity explicit as an almost-everywhere property at each time. Then convert expectation constancy into a bound on the L¹ norm. This is usually shorter and more robust than trying to prove a pointwise upper bound for the martingale.

## 9. A norm criterion for uniform integrability

On a probability space, a uniform Lᵖ bound for some `p > 1` is a common sufficient condition for uniform integrability. The estimate is elementary. For a threshold `K > 0`, on the tail event `|f n| > K` one has

\[
  |f_n| \leq K^{1-p}|f_n|^p.
\]

Therefore

\[
  \int_{\{|f_n|>K\}} |f_n|\,dP
  \leq K^{1-p}\int |f_n|^p\,dP.
\]

If the pth moments are bounded uniformly in `n`, the right side tends to zero uniformly as `K` grows. This is exactly the tail control required for uniform integrability. For `p=2`, a uniform second-moment estimate is often convenient because it can be obtained from orthogonality or variance calculations.

In Lean, state the moment bound in a form the library recognizes, prove the tail estimate using the pointwise inequality on the measurable tail set, and apply the theorem connecting Lᵖ boundedness to uniform integrability. The precise typeclass assumptions depend on the measure and exponent; on a probability space they are especially natural. This route is preferable to unfolding the definition of uniform integrability in every later convergence proof.

The criterion is sufficient, not necessary. A uniformly integrable family need not have a uniform pth moment for any `p > 1`. If the problem gives tail bounds directly, use the uniform-integrability interface rather than forcing a stronger moment estimate.

## 10. A proof workflow

1. Decide whether the goal is almost-everywhere convergence or L¹ convergence.
2. State the process as a submartingale or martingale with respect to a filtration.
3. Establish strong adaptation and integrability in the form required by that predicate.
4. For a.e. convergence, prove a uniform L¹ norm bound.
5. For L¹ convergence, prove uniform integrability and identify the terminal measurable space.
6. Use the limit-process theorem rather than constructing a representative before it is needed.
7. For conditional-expectation martingales, exploit the fixed integrable terminal variable to obtain uniform integrability.
8. Keep all final conclusions in their correct mode: almost everywhere, in probability, or in L¹.

This workflow makes the analytic part of the argument explicit before the convergence theorem is applied. It also helps separate pathwise facts from expectation estimates, which often require different lemmas and different measure-theoretic assumptions.

For maintainability, preserve these intermediate facts as named lemmas: a norm bound for each process value, the uniform bound across indices, the limit-process convergence statement, and the identification of the limit when a formula is known. A later proof can then reuse the analytical estimate without unfolding the martingale predicate or repeating the upcrossing argument. This separation is especially useful when the same process is studied under several filtrations or when an argument later upgrades almost-sure convergence to L¹ convergence.

## 11. Common failure modes

### L¹ boundedness is mistaken for uniform integrability

L¹ boundedness controls the norms but not the tails uniformly. It supports the a.e. theorem, not every L¹ convergence conclusion.

### A signed integral bound is used as an absolute-value bound

Cancellation can make `∫ f n` small while `∫ |f n|` is large. State the norm bound required by `L1Bounded`.

### Almost-everywhere convergence is upgraded without proof

Use uniform integrability or another valid convergence theorem to obtain L¹ convergence.

### Adaptedness is omitted

The limit theorem applies to a process with the required strong adaptation to the filtration, not an arbitrary sequence of integrable functions.

### The terminal σ-algebra is ignored

Conditional predictions recover only information measurable with respect to `ℱ∞`. Verify terminal measurability before claiming convergence to a proposed variable.

### A pointwise bound is sought unnecessarily

L¹ boundedness and uniform integrability are integral conditions. They are often the natural estimates even when the variables have unbounded support.

## 12. Exercises

1. Distinguish almost-everywhere convergence from L¹ convergence.
2. State the L¹ boundedness condition for a process.
3. Explain why an L¹-bounded real submartingale converges almost everywhere.
4. Describe how infinitely many upcrossings of a rational interval obstruct convergence.
5. State the role of uniform integrability in the L¹ martingale convergence theorem.
6. Define the terminal filtration `ℱ∞` and explain its relation to adaptedness.
7. Show why a conditional-expectation process of a fixed integrable terminal variable is a natural martingale-convergence example.
8. Give an example pattern where almost-sure convergence does not imply convergence of expectations.
9. Explain why nonnegativity plus constant expectation yields L¹ boundedness but not necessarily uniform integrability.
10. Locate Mathlib's `ae_tendsto_limitProcess` theorem and list its adaptation and boundedness assumptions.

## Summary

L¹ boundedness gives almost-everywhere convergence for strongly adapted submartingales through an upcrossing argument. Uniform integrability controls tails and upgrades this to L¹ convergence. The limit is measurable with respect to the filtration generated over all finite times. Conditional expectations of a terminal integrable variable form a uniformly integrable martingale that converges back to that variable when it is measurable with respect to the terminal filtration. Keep the convergence mode and its analytic hypotheses explicit.

## Further reading

- [Mathlib: Martingale convergence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Convergence.html)
- [Mathlib: Uniform integrability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/UniformIntegrable.html)
- [Mathlib: Martingales](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Basic.html)
