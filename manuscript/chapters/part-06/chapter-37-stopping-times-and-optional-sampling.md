# Chapter 37 — Stopping Times and Optional Sampling

> **Audience.** This chapter assumes familiarity with filtrations, adapted processes, conditional expectation, and martingales. It develops stopping-time measurability, stopped processes, bounded optional sampling, and maximal estimates.

Stopping times let a decision depend on the information revealed so far. One can stop a process when it first reaches a target, when a loss becomes too large, or when a data-dependent condition is met. The mathematical condition is local in time: whether stopping has occurred by time `n` must be decidable using the information available at time `n`.

Optional sampling then compares the expected values of a process at ordered stopping times. The theorem is powerful precisely because it has hypotheses. In Lean, the stopping-time property, boundedness, filtration, adaptation, and integrability appear as distinct assumptions. Keeping them separate helps distinguish a valid fair-game argument from an unjustified appeal to intuition.

This chapter uses discrete time indexed by `ℕ`, the setting of the principal Mathlib optional-stopping theorem discussed here. Other index types require the corresponding order and topology assumptions of their APIs.

## Learning objectives

By the end of the chapter, you should be able to:

- state stopping-time measurability relative to a filtration;
- explain how a stopped process freezes at a random time;
- apply bounded optional sampling to submartingales and martingales;
- distinguish a stopping time from an arbitrary random time;
- identify where boundedness and integrability enter a formal theorem;
- use maximal inequalities to control the probability of large excursions.

## 1. A stopping time is relative to information

Let `ℱ` be a filtration and let `τ : Ω → WithTop ℕ` be a possibly infinite random time. It is a stopping time when, for each `n`, the event that stopping has happened by time `n` is measurable using `ℱ n`:

\[
  \{\omega \mid \tau(\omega) \leq n\}\in\mathcal{F}_n.
\]

Mathlib packages this as `IsStoppingTime ℱ τ`. The codomain `WithTop ℕ` accommodates the value `⊤`, representing a time that never occurs. The condition is checked at every finite time; the function `τ` is not required to be measurable as a map into an arbitrary measurable space of times.

The filtration is essential. A time can be a stopping time for a rich filtration and fail to be one for a poorer filtration. The condition does not say that the future stopping time is known now. It says that the decision “have we stopped yet?” can be made now.

```text
At time n, the observer knows ℱ n.
          │
          ├── can decide whether τ ≤ n ──▶ τ is a stopping time
          └── needs information after n ─▶ τ may not be a stopping time
```

For example, the first time a random walk reaches level `a` is a stopping time: by time `n`, one can inspect the path up to `n` and determine whether the level has already been reached. The last time before `n` that the path reaches `a` is a different kind of object. Deciding that a visit was the last one may require looking into the future, so it is not generally a stopping time.

In a formal proof, establish the event-measurability property at the boundary where the random time is defined. This is usually easier than trying to prove all stopping-time obligations after constructing a stopped process. A first-hitting-time definition often comes with a theorem that packages precisely this property.

## 2. Stopped values and stopped processes

Given a process `f` and stopping time `τ`, the stopped value at deterministic horizon `n` evaluates `f` at the earlier of `τ` and `n`. In ordinary notation,

\[
  f_{\tau\wedge n}(\omega) = f_{\min(\tau(\omega),n)}(\omega).
\]

Mathlib uses `stoppedValue` for this value. The stopped process records it as the horizon changes. Before `τ`, it follows the original process; after `τ`, it remains fixed.

```text
path f(ω):          •──•──•──•──•──•──•
stopping time τ:              ▲
stopped path:     •──•──•──•──┴──┴──┴
                              value is frozen
```

If `f` is adapted and `τ` is a stopping time, the stopped process is adapted under the usual hypotheses. This is a structural result: at time `n`, the stopped value can be determined from the observations available up to `n`, because the observer can determine whether `τ ≤ n` and can read the process through time `n`.

Do not confuse the stopped process with the original process evaluated at an unbounded random index. The `WithTop` representation requires careful handling of `⊤`, and the stopped-value construction explicitly retains a deterministic horizon. In bounded optional-sampling arguments, the horizon gives a finite range in which all values are controlled.

## 3. Bounded stopping times

A stopping time `τ` is bounded if there exists a deterministic `N` such that

\[
  \tau(\omega) \leq N \quad\text{for every }\omega.
\]

This is a uniform bound, not merely an almost-sure bound. It says every sample path stops by the same deterministic time. That uniformity is what makes the elementary optional-sampling theorem safe: the stopped value can be expressed using finitely many increments, and all integrability obligations reduce to finitely many process values.

Some theorems can be stated under weaker hypotheses, such as almost-sure boundedness or uniform integrability of a family of stopped variables. Use the theorem matching the available assumptions. Do not silently weaken the bound in a theorem application because probability-one statements often require additional completion or modification arguments.

In Lean, the bound is commonly expressed as an existential natural number with a pointwise inequality into `WithTop ℕ`. When reading a theorem signature, distinguish this from a statement that `τ` is finite almost everywhere. These conditions are related in some contexts but are not interchangeable without proof.

## 4. Optional sampling for submartingales

Let `f` be a strongly adapted, integrable process indexed by `ℕ`. If `f` is a submartingale and `τ ≤ π` are bounded stopping times, then

\[
  \mathbb{E}[f_\tau] \leq \mathbb{E}[f_\pi].
\]

For a martingale, apply the corresponding submartingale comparison in both directions to obtain equality of expectations. This is the bounded optional-sampling principle: observing a fair game and stopping according to available information does not change its expectation, while a submartingale's expected stopped value does not decrease as the stopping time increases.

Mathlib's `submartingale_iff_expected_stoppedValue_mono` characterizes the submartingale property using the expected-value inequality for all ordered bounded stopping times. Its hypotheses include strong adaptation, integrability at every deterministic time, and the filtration finiteness condition. The right-hand side uses `stoppedValue` and a common deterministic bound on the later stopping time.

This theorem can be useful in two directions. If a process is already known to be a submartingale, it yields an expectation comparison at chosen stopping times. Conversely, if the stopped-value inequalities are easier to prove, the characterization can establish the submartingale property. In either direction, check whether the theorem expects ordered stopping times `τ ≤ π`, and whether its integrability assumptions are pointwise in the time index.

The formal proof should not hide the stopping-time proofs inside the final theorem call. Build each time with the filtration in scope, prove its measurability property, prove the deterministic bound, and then pass these facts to the optional-sampling result. This keeps the mathematical argument visible and avoids a cascade of unrelated goals.

## 5. Worked example: a bounded fair random walk

Consider a simple symmetric random walk `S n` with `S 0 = 0` and increments `+1` or `−1` of conditional mean zero given the previous information. The martingale-difference criterion shows that `S` is a martingale. Let `τ` be the first time the walk hits either boundary `−a` or `a`, and truncate it at a fixed horizon `N`:

\[
  \tau_N = \tau \wedge N.
\]

The first-hit time is a stopping time, and its truncation is bounded by `N`. Optional sampling therefore gives

\[
  \mathbb{E}[S_{\tau_N}] = \mathbb{E}[S_0] = 0.
\]

The event “the walk hits `a` before `−a` and by time `N`” contributes `a` to the stopped value. The event of hitting `−a` contributes `−a`; paths that hit neither boundary by `N` contribute their position at `N`, which can be strictly inside the interval. The zero expectation equation balances these contributions.

For a Lean formalization, avoid starting with a closed-form hitting probability. First package the path space and coordinate process; prove the coordinate process is a martingale from its increments; prove the first-hit event condition; truncate; and invoke optional sampling. If the desired result is the probability of hitting one boundary first, a separate limit argument may be needed to let `N` grow. Optional sampling at each finite `N` alone does not justify passing to an unbounded stopping time.

This example illustrates the theorem's division of labor. Martingale structure comes from conditional means of increments. Stopping-time measurability comes from path information. The optional-sampling theorem combines them only after boundedness and integrability have been supplied.

## 6. Worked example: monotone expected values at ordered stops

Suppose `f` is a submartingale and `τ` and `π` are bounded stopping times with `τ ≤ π`. Optional sampling gives

\[
  \mathbb{E}[f_\tau] \leq \mathbb{E}[f_\pi].
\]

The proof does not require the stopping times to be deterministic or independent of the process. Their dependence on the path is allowed precisely because each is a stopping time. As a simple instance, take `τ = 0` and `π = N` for a deterministic horizon. The inequality reduces to the familiar monotonicity of expectations of a submartingale.

Now let `π` be the first time a process reaches a threshold, capped at `N`, and let `τ` be an earlier bounded stopping time. The theorem compares values at these path-dependent times without enumerating every path. This is the payoff of the bundled stopping-time interface.

When a goal is already phrased as an expectation of a stopped value, apply the theorem directly. When it is phrased as an integral over an event, first express the event through the stopping time or use a maximal inequality; do not expand `stoppedValue` unless the pathwise definition is genuinely needed.

## 7. A conditional-expectation form of sampling

For a martingale and a bounded stopping time `τ ≤ n`, the stopped value has a stronger description: it is almost everywhere the conditional expectation of the terminal value `f n` with respect to the information generated by `τ`. Mathlib documents this through `stoppedValue_ae_eq_condExp_of_le_const`.

This formulation explains why stopping preserves expectation. Integrating a conditional expectation over the whole space gives the integral of the original terminal variable, so the expected stopped value agrees with the expected terminal value. It also gives more information than an equality of expectations: it identifies the stopped value as a prediction based on the stopping-time information.

The exact measurable space generated by a stopping time and the theorem's side conditions should be read from the current API. In particular, sigma-finiteness assumptions may appear for the trimmed measure. Prefer this conditional formulation when the goal concerns information available at the stopping time; use the expectation comparison when only the mean is needed.

## 8. Doob's maximal inequality

Optional-stopping libraries also connect submartingales to maximal bounds. For a nonnegative submartingale, the probability that its running maximum reaches a threshold is controlled by an expectation involving its value at the terminal horizon. A standard schematic form is

\[
  \varepsilon\,P\!\left(\max_{k\leq n} f_k\geq\varepsilon\right)
  \leq \int_{\{\max_{k\leq n} f_k\geq\varepsilon\}} f_n\,dP.
\]

Mathlib includes Doob's maximal inequality alongside the optional-stopping results. The running maximum is over finitely many times, so its measurability and finiteness are approachable with finite-index arguments. The theorem is especially useful when a convergence proof needs to show that large excursions occur only on a small event.

Be precise about the form of the inequality available. The displayed expression is meant to communicate the structure; the library may use `ℝ≥0`, scalar multiplication, a supremum or finite maximum, and a threshold convention with strict versus non-strict inequality. Match the theorem statement exactly rather than repairing a mismatch with `simp` before checking the mathematical boundary cases.

## 9. A proof workflow

1. Specify the filtration and the time type before defining the stopping rule.
2. Prove `{τ ≤ n}` measurable in `ℱ n` for every deterministic `n`.
3. Establish strong adaptation and integrability of the process.
4. Prove a common deterministic bound for every stopping time in the argument.
5. Order the stopping times in the direction required by the theorem.
6. Use `stoppedValue` for stopped observations and the conditional-expectation theorem when the information at stopping matters.
7. For tail estimates, choose a maximal inequality with the same threshold and maximum convention as the goal.
8. If removing a bound by taking a limit, prove the required convergence or uniform-integrability condition separately.

This workflow avoids a common proof-engineering trap: proving that a candidate time is finite and measurable only after all subsequent constructions already depend on it. Define the stopping time's interface first, and the stopped-process API can then use that interface compositionally.

## 10. Common failure modes

### A random time is called a stopping time without a filtration

Stopping-time measurability is always relative to `ℱ`. Name the filtration in the definition and proof.

### The event uses future information

Prove the event `{τ ≤ n}` is measurable at time `n`. The event that `n` is the last visit to a set usually depends on future observations.

### A pointwise finite time is mistaken for a bounded time

Optional sampling may require one deterministic bound that works for every outcome. Pointwise finiteness alone is not enough.

### Optional sampling is applied to an arbitrary process

Supply adaptation, integrability at every index, and the martingale or submartingale property as required.

### A theorem for submartingales is used as an equality

The generic result gives an inequality. Equality for martingales uses both directions or a theorem stated specifically for martingales.

### A finite-horizon argument is used for an unbounded stopping time

Truncate first, then justify passage to the limit with an appropriate convergence theorem. The limit is a separate mathematical step.

## 11. Exercises

1. State the stopping-time measurability condition for `τ : Ω → WithTop ℕ`.
2. Explain why the first hitting time of a measurable state set is typically a stopping time, but the last hitting time is not.
3. Define the stopped value at a deterministic horizon `n` in mathematical notation.
4. State bounded optional sampling for a submartingale and identify the pointwise bound required for the later stopping time.
5. Deduce expectation preservation for a martingale from the submartingale comparison in both directions.
6. For a simple random walk stopped at the first hit of `±a` or at horizon `N`, identify the stopping-time and boundedness lemmas needed before applying optional sampling.
7. Explain how a conditional-expectation representation of a stopped martingale implies equality of expectations.
8. State the qualitative content of Doob's maximal inequality and describe an application to tail control.
9. Explain why bounded optional sampling at every `N` does not alone justify sampling at an unbounded stopping time.
10. Locate `submartingale_iff_expected_stoppedValue_mono` and list its filtration and process assumptions.

## Summary

A stopping time is a random time whose occurrence by each deterministic horizon is measurable using the information available by then. Stopped processes freeze at that time. Bounded optional sampling compares expected stopped values of ordered stopping times for submartingales and yields equality for martingales. Mathlib's API makes stopping-time measurability, bounds, adaptation, integrability, and filtration conditions explicit. Maximal inequalities extend the same machinery to control large excursions.

## Further reading

- [Mathlib: Optional stopping](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/OptionalStopping.html)
- [Mathlib: Optional sampling](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/OptionalSampling.html)
- [Mathlib: Stopping times](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Stopping.html)
