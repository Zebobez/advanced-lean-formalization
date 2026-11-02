# Chapter 39 — Predictable Processes and Doob Decomposition

> **Audience.** This chapter assumes familiarity with filtrations, martingales, conditional expectation, and stopping times. It develops predictable processes and the discrete-time decomposition of an adapted integrable process into a martingale and a predictable component.

A martingale is the part of a process that remains after its predictable drift has been removed. In discrete time, the drift at step `n` is the conditional expectation of the next increment given the information at time `n`. Subtracting this conditional mean leaves an increment with conditional expectation zero, which is exactly the martingale-difference condition.

This decomposition is often called Doob decomposition. It is useful both as a theorem and as a proof design pattern: replace a difficult process by a centered fluctuation plus an information-measurable accumulated drift. Mathlib exposes the components as `predictablePart` and `martingalePart` for ℕ-indexed processes.

The word “predictable” has a precise time convention. In discrete time, a predictable process's value at time `n+1` is measurable using information at time `n`. That one-step shift is essential. An adapted process at time `n+1` may use the new information revealed between `n` and `n+1`; a predictable process may not.

## Learning objectives

By the end of the chapter, you should be able to:

- state predictability in discrete time using the preceding σ-algebra;
- form the conditional drift of each process increment;
- derive the martingale and predictable parts from those increments;
- apply Mathlib's `predictablePart` and `martingalePart` interfaces;
- recognize a submartingale's predictable part as an increasing process;
- distinguish this discrete-time result from continuous-time Doob–Meyer theory.

## 1. Predictable means known one step earlier

Let `ℱ` be a filtration indexed by `ℕ`. A process `A` is predictable when each value at time `n+1` is measurable with respect to `ℱ n`, together with the initial measurability condition at zero. Mathlib packages this as `IsStronglyPredictable ℱ A`; `IsStronglyPredictable.iff_measurable_add_one` exposes the discrete-time characterization.

The indexing reflects the information flow:

```text
time n                         time n+1
information ℱ n ──▶ new data ──▶ information ℱ (n+1)
      │
      └── can determine A (n+1) if A is predictable
```

Predictability implies adaptedness, but not conversely. An adapted process at time `n+1` is allowed to depend on the new data revealed at that time. A predictable process must already be determined at time `n`.

This is the natural measurability condition for a drift accumulated over the next interval. If the value `A (n+1) - A n` represents the expected change during step `n`, that expected change is known from the information available at time `n`.

In Lean, the index shift is not cosmetic. To prove that `A` is predictable, show measurability of `A (n+1)` with respect to `ℱ n`; proving only that it is measurable with respect to `ℱ (n+1)` establishes adaptedness, which is weaker.

## 2. Conditional drift of an increment

For an integrable process `f`, write its increment as

\[
  \Delta f_n = f_{n+1}-f_n.
\]

The conditional drift is

\[
  d_n = \mathbb{E}[\Delta f_n\mid\mathcal{F}_n].
\]

It is measurable with respect to the information available at time `n`. Summing these conditional drifts gives the predictable component:

\[
  A_0=0,\qquad A_n=\sum_{i<n}d_i.
\]

The centered increment is `Δfₙ − dₙ`. By linearity and the defining property of conditional expectation, its conditional expectation given `ℱ n` is zero. The cumulative centered process is therefore a martingale after retaining the initial value:

\[
  M_0=f_0,\qquad
  M_n=f_0+\sum_{i<n}(\Delta f_i-d_i).
\]

Adding the two components recovers the original process:

\[
  f_n=M_n+A_n.
\]

```text
increment Δfₙ
    │
    ├── conditional mean given ℱₙ ──▶ predictable drift dₙ
    │
    └── subtract dₙ ────────────────▶ martingale difference
                    │                         │
                    ▼                         ▼
              accumulated Aₙ            accumulated Mₙ
                    └──────── Mₙ + Aₙ = fₙ ──┘
```

## 3. The Mathlib construction

For a process `f : ℕ → Ω → E`, filtration `ℱ`, and measure `μ`, Mathlib defines `predictablePart f ℱ μ` and `martingalePart f ℱ μ`. The predictable component has the formula

\[
  \operatorname{predictablePart}(f,\mathcal{F},\mu)_n
  =\sum_{i<n}\mu[f_{i+1}-f_i\mid\mathcal{F}_i],
\]

and the martingale component is the original process minus that predictable part. The theorem `martingalePart_add_predictablePart` states that their sum is `f`.

Under the theorem's assumptions, `martingale_martingalePart` proves that the centered component is a martingale. The predictable component is recognized by `isPredictable_predictablePart` (the newer API uses `IsStronglyPredictable`; older source names may still appear as deprecated aliases). The process values are integrable, and the filtration must meet the sigma-finiteness assumptions required by the martingale result.

The construction works in a complete real normed vector space with the relevant integrability assumptions. The formula is mathematically familiar, but the library theorem is valuable because it packages the measurable, integrable, and almost-everywhere conditional-mean arguments once. Apply it at the process level instead of rebuilding each finite sum in every application.

## 4. Worked example: centering a process

Suppose `f` is strongly adapted and each `f n` is integrable. Define

\[
  A_n=\sum_{i<n}\mathbb{E}[f_{i+1}-f_i\mid\mathcal{F}_i],
  \qquad M_n=f_n-A_n.
\]

To verify the decomposition, observe that `A₀=0`, and

\[
  A_{n+1}-A_n=\mathbb{E}[f_{n+1}-f_n\mid\mathcal{F}_n].
\]

Then

\[
  M_{n+1}-M_n
  =(f_{n+1}-f_n)-\mathbb{E}[f_{n+1}-f_n\mid\mathcal{F}_n].
\]

Conditioning on `ℱ n` yields zero. This one-step identity, together with adaptation and integrability, proves that `M` is a martingale. The predictable part follows from the measurability of each conditional drift at time `n`.

In Lean, a maintainable proof establishes the recurrence for `predictablePart` first, then rewrites the increment of `martingalePart` using that recurrence. The conditional-expectation subtraction theorem closes the one-step martingale identity. The full theorem `martingale_martingalePart` already performs this reasoning when its hypotheses match, so the manual proof is mainly useful when deriving a specialized variant or understanding a failed application.

As a concrete model, let the update rule be

\[
  X_{n+1}=X_n+b_n+\varepsilon_{n+1},
\]

where `b n` is `ℱ n`-measurable and the noise has conditional mean zero given `ℱ n`. Then the conditional drift of the increment is `b n`. The predictable component is `A n = ∑ i < n, b i`, and the martingale component is `M n = X 0 + ∑ i < n, ε (i+1)`. The equality `X n = M n + A n` follows by telescoping the update equation.

An autoregressive update with drift proportional to the current state is a common special case: when `X n` is `ℱ n`-measurable, `b n = θ * X n` is predictable. The decomposition separates the state-dependent systematic drift from the centered innovation. In code, prove the conditional-mean-zero property of each noise term once, then use finite-sum lemmas to establish the process-level equality.

## 5. Worked example: a submartingale accumulates nonnegative drift

Suppose `f` is a real submartingale. By definition,

\[
  f_n\leq\mathbb{E}[f_{n+1}\mid\mathcal{F}_n]
  \quad\text{almost surely}.
\]

Because `f n` is measurable with respect to `ℱ n`, its conditional expectation given `ℱ n` agrees with `f n`. Subtracting gives

\[
  0\leq\mathbb{E}[f_{n+1}-f_n\mid\mathcal{F}_n]
  \quad\text{almost surely}.
\]

Each drift increment is nonnegative almost surely. A countable intersection of the full-measure events lets us conclude that, almost surely, the predictable component is monotone in time. Mathlib exposes this through `Submartingale.monotone_predictablePart` and a nonnegativity result for its values.

Thus a submartingale decomposes into a martingale fluctuation and an increasing predictable trend. This is useful for interpreting the source of submartingale growth: the centered component is fair relative to current information, and the predictable component accounts for the nonnegative conditional drift.

The almost-everywhere qualifier should be retained. Each step's drift inequality is an a.e. statement; obtaining one set on which all countably many steps hold uses countability of `ℕ` and the measure-theoretic API for countable intersections.

## 6. Worked example: decomposition of a martingale

If `f` is already a martingale, then for each `n`,

\[
  \mathbb{E}[f_{n+1}-f_n\mid\mathcal{F}_n]=0
  \quad\text{almost surely}.
\]

Every increment in `predictablePart` is therefore zero almost everywhere, so `predictablePart f ℱ μ n = 0` almost everywhere for each `n`. The martingale component agrees almost everywhere with `f`. Mathlib provides `Martingale.predictablePart_eq_zero` and `Martingale.martingalePart_eq` for these reductions.

This is an important simplification rule: when the input already has zero conditional drift, the decomposition introduces no new finite-sum reasoning. It also serves as a useful consistency check for definitions. A proposed decomposition that assigns nonzero predictable drift to a martingale likely has an index or sign error.

## 7. Worked example: a purely predictable process

Suppose `f` is predictable. Then `f (n + 1)` is measurable with respect to `ℱ n`, and `f n` is also measurable there because the filtration is increasing. Hence the increment `f (n + 1) - f n` is already known at time `n`; conditioning it on `ℱ n` leaves it unchanged almost everywhere. The accumulated drift telescopes:

\[
  A_n=\sum_{i<n}(f_{i+1}-f_i)=f_n-f_0.
\]

Consequently, `M n = f n - A n = f 0` almost everywhere. The martingale part of a predictable process is just its initial value. Mathlib states this through `IsStronglyPredictable.martingalePart_eq`, under the integrability and filtration assumptions shown in that theorem.

This is the counterpart to the previous example. A martingale has zero predictable drift; a predictable process has no new martingale fluctuation after its initial value. The decomposition separates two extremes cleanly and provides useful simplification lemmas for mixed processes.

## 8. Uniqueness and reuse

The increment formula explains why this decomposition is determined by the original process and the filtration. Each predictable increment must be the conditional expectation of the corresponding process increment. If another decomposition has a predictable component `B` and a martingale component `N`, with the same initial-value normalization, compare the increments. The difference between the two proposed drift components is both predictable and a martingale. A predictable martingale is constant almost everywhere; since both drift parts start at zero, that difference vanishes almost everywhere.

This uniqueness argument is often more useful than unfolding the explicit finite sum. To prove that a hand-built pair of processes agrees with Mathlib's pair, verify that the first is predictable, the second is a martingale, their sum is the original process, and their initial values match. The library characterization then identifies the components up to almost-everywhere equality.

In a larger development, keep the decomposition as a named process-level lemma. Later results may use only that `martingalePart` is a martingale or that `predictablePart` is predictable and increasing; they need not know how its finite sum is implemented. This is the same abstraction boundary used for bundled maps and conditional expectation elsewhere in the book.

## 9. Discrete predictable processes and terminology

Predictability is stronger than adaptation and is also distinct from independence. A predictable drift may depend on the entire past, as long as its next value is already measurable at the current time. It need not be deterministic and need not be independent of the process.

In continuous-time probability, predictability is defined using a σ-algebra on time and sample space generated by adapted left-continuous processes. The discrete-time one-step characterization is a concrete instance of the same information principle, but results do not transfer automatically between the discrete and continuous APIs. The `Centering` file discussed here is specifically indexed by `ℕ`; it should not be presented as the general continuous-time Doob–Meyer theorem.

The term “Doob decomposition” is used for several closely related results. In this chapter it means the canonical discrete-time decomposition formed from conditional expectations of increments. In more advanced continuous-time theory, a submartingale is decomposed into a martingale and a predictable increasing process under additional regularity hypotheses. Keep the index type and theorem assumptions explicit when moving between sources.

## 10. Using the bundled theorem

When the construction fits the library's general result, prepare its inputs as named facts: `StronglyAdapted ℱ f`, integrability of every `f n`, completeness of the value space where required, and the sigma-finiteness condition for the filtration. Then use `martingale_martingalePart` to establish the martingale property and `isPredictable_predictablePart` or its current strongly-predictable name for the drift. Use `martingalePart_add_predictablePart` to recover the process.

If one assumption is unavailable, do not try to force a weaker notion into the theorem with casts. First determine whether the application actually needs the full decomposition. A scalar identity may follow directly from conditional expectation; a process theorem may need strong measurability rather than ordinary measurability. The theorem signatures distinguish these cases.

This way of organizing a proof keeps the final application short without hiding the mathematics. The setup lemmas document the model's regularity; the bundled theorem supplies the generic construction; and downstream results can consume only the component property they need.

## 11. A proof workflow

1. Fix the filtration and the discrete time convention.
2. Prove strong adaptedness and integrability of each process value.
3. Form increments as `f (n + 1) - f n`.
4. Take conditional expectation with respect to `ℱ n` to define the drift.
5. Use the finite-sum formula for `predictablePart` or invoke the bundled construction.
6. Prove the centered increment has conditional expectation zero.
7. Use the theorem that the martingale part is a martingale.
8. For a submartingale, turn the defining inequality into nonnegative conditional drift.
9. State decomposition identities as pointwise equalities where definitional, and a.e. equalities where conditional expectations are involved.

The most common Lean issue is an off-by-one mismatch: the drift for the step from `n` to `n+1` is measurable at `n`, and predictability therefore concerns the value at `n+1`. Keep the recurrence and its indices visible in intermediate lemmas.

## 12. Common failure modes

### Adaptedness is treated as predictability

Adaptedness allows dependence on information at the current time. Predictability of the next value uses the preceding σ-algebra.

### The increment is reversed

The convention here is `f (n + 1) - f n`. Reversing it changes the sign of both the predictable drift and the martingale difference.

### Integrability is omitted

Conditional expectations of increments require integrability. Prove integrability of each process value and then of each difference.

### A.e. identities are used as pointwise identities

The conditional drift and centered-increment equations hold almost everywhere. Use the measure-indexed equality and order relations.

### A discrete theorem is generalized to continuous time

The construction and predictable σ-algebra are index-sensitive. Check the theorem's index type and hypotheses.

## 13. Exercises

1. State the discrete-time characterization of `IsStronglyPredictable`.
2. Given `f`, define its increment and conditional drift at time `n`.
3. Derive the recurrence for `predictablePart f ℱ μ (n + 1)`.
4. Show that the centered increment has conditional expectation zero.
5. Explain how the initial value `f 0` appears in the martingale part.
6. Use the submartingale inequality to show each predictable drift increment is nonnegative almost everywhere.
7. Explain why the predictable part of an existing martingale is zero almost everywhere.
8. Find `martingalePart_add_predictablePart` and `martingale_martingalePart`; list the assumptions used in your context.
9. Compare the discrete-time decomposition in this chapter with the continuous-time Doob–Meyer theorem.
10. Identify an index shift that would make an adaptedness proof insufficient to establish predictability.

### 13.1 Compiled Doob-decomposition patterns

The finite-state example computes the residual after subtracting the proposed predictable drift using exact integer arithmetic:

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def rawIncrement : State → Int := fun s => if s = zero then -1 else 1
def predictableDrift : State → Int := rawIncrement
def martingaleResidual (s : State) : Int := rawIncrement s - predictableDrift s

theorem residualAtZero : martingaleResidual zero = 0 := by decide
theorem residualAtOne : martingaleResidual one = 0 := by decide
```

The predictable component satisfies a one-step recurrence: its next value adds the conditional mean of the process increment.

```lean
open MeasureTheory
open scoped MeasureTheory ProbabilityTheory

theorem exercise_39_3_predictablePart_recurrence
    {Ω E : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℱ : Filtration ℕ m₀) (f : ℕ → Ω → E) (n : ℕ) :
    predictablePart f ℱ μ (n + 1) =
      predictablePart f ℱ μ n + μ[f (n + 1) - f n | ℱ n] := by
  exact predictablePart_add_one n
```

The two constructed parts sum to the original process by definition:

```lean
open MeasureTheory

theorem exercise_39_8_doob_decomposition_identity
    {Ω E : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℱ : Filtration ℕ m₀) (f : ℕ → Ω → E) :
    martingalePart f ℱ μ + predictablePart f ℱ μ = f := by
  exact martingalePart_add_predictablePart ℱ μ f
```

If the original process is strongly adapted, each time slice is integrable, and the filtration is σ-finite under the measure, Mathlib proves that the martingale component is a martingale:

```lean
open MeasureTheory

theorem exercise_39_8_martingalePart_is_martingale
    {Ω E : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ℱ : Filtration ℕ m₀) (f : ℕ → Ω → E)
    (hadapted : StronglyAdapted ℱ f) (hint : ∀ n, Integrable (f n) μ)
    [SigmaFiniteFiltration μ ℱ] :
    Martingale (martingalePart f ℱ μ) ℱ μ := by
  exact martingale_martingalePart hadapted hint
```

For an existing martingale, the predictable component is zero almost everywhere at every time:

```lean
open MeasureTheory

theorem exercise_39_7_predictablePart_of_martingale
    {Ω E : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ℱ : Filtration ℕ m₀} {f : ℕ → Ω → E}
    (hf : Martingale f ℱ μ) (n : ℕ) :
    predictablePart f ℱ μ n =ᵐ[μ] (0 : Ω → E) := by
  exact hf.predictablePart_eq_zero n
```

## Summary

In discrete time, predictability means that the next process value is measurable using current information. The conditional expectation of each increment is the predictable drift; subtracting it leaves a martingale difference. Summing these parts yields Mathlib's `predictablePart` and `martingalePart`, whose sum recovers the original process. For a submartingale, the predictable part is increasing almost surely; for a martingale, it vanishes almost surely. Keep the time shift, integrability, and a.e. status explicit.

## Further reading

- [Mathlib: Doob decomposition and centering](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Centering.html)
- [Mathlib: Predictable processes](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Predictable.html)
- [Mathlib: Martingales](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Basic.html)
