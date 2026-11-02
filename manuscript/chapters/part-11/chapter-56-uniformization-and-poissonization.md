# Chapter 56 — Uniformization and Poissonization

> **Audience.** This chapter assumes familiarity with finite-state Markov chains, continuous-time generators, matrix exponentials, and infinite sums. It develops uniformization as both a probabilistic construction and a proof technique for finite-state chains.

Uniformization replaces continuous-time evolution by a discrete transition matrix observed at the events of an independent Poisson clock. The clock may ring without changing the state; such a ring is a self-transition. This construction is mathematically equivalent to the matrix exponential of a finite generator, but it exposes nonnegativity and conservation of probability term by term.

The method is useful in formalization because the main stochasticity obligations become modular. A single rate bound makes one discrete matrix stochastic. Every power of that matrix is then stochastic, and a probability-weighted sum of those powers remains stochastic. The infinite sum still requires convergence and interchange arguments, but its terms have a transparent sign and interpretation.

## Learning objectives

By the end of the chapter, you should be able to:

- choose a uniform rate bound for a finite generator;
- construct the associated stochastic matrix;
- express the transition semigroup as a Poisson mixture;
- prove stochasticity without inferring positivity from the matrix exponential;
- connect the mixture to the exponential representation;
- interpret self-transitions as discarded Poisson events;
- organize the finite and infinite-sum obligations in Lean.

## 1. The uniformization idea

Let `S` be a finite state space and let `Q : Matrix S S ℝ` be a generator. Write
\[
  \lambda(x)=\sum_{y\ne x}q_{xy}
\]
for the exit rate from state `x`. Since `S` is finite, the exit rates have a finite maximum. Choose a constant `Λ > 0` satisfying
\[
  \lambda(x)\leq\Lambda\quad\text{for every }x\in S.
\]
Define
\[
  R=I+\frac{Q}{\Lambda}.
\]
For distinct states, `R(x,y)=q_{xy}/Λ`, which is nonnegative. On the diagonal,
\[
  R(x,x)=1-\frac{\lambda(x)}{\Lambda}\geq0.
\]
The row sum of `R` is
\[
  \sum_yR(x,y)=1+\frac1\Lambda\sum_yq_{xy}=1.
\]
Thus `R` is a stochastic matrix.

The transition family of the continuous-time chain is
\[
  P_t=e^{tQ}
      =e^{-\Lambda t}\sum_{n=0}^{\infty}
        \frac{(\Lambda t)^n}{n!}R^n,\qquad t\geq0.
\]
The coefficient is the probability that a Poisson random variable with mean `Λt` equals `n`. Conditional on `n` clock rings in the time interval, the state evolves by `n` applications of `R`. The matrix `R` is the transition rule at a clock ring, not necessarily the transition rule at a genuine jump of the chain.

If every exit rate is zero, then `Q=0` and the chain never moves. Any positive `Λ` gives `R=I` and the displayed mixture reduces to `I`. This edge case is mathematically harmless, but treating it explicitly can simplify constructions that define `Λ` as a maximum.

## 2. Why the discrete matrix is stochastic

Uniformization begins with a finite sign check. A formal proof typically separates it into three lemmas:

1. `Λ` is positive;
2. each entry of `R` is nonnegative;
3. every row of `R` sums to one.

For diagonal nonnegativity, use the bound `λ(x) ≤ Λ` and divide by the positive `Λ`. For off-diagonal nonnegativity, divide the generator rate inequality by `Λ`. The row-sum proof expands `R=I+Q/Λ`, applies the generator's row-sum equation, and simplifies.

This decomposition is more reusable than proving directly that the matrix exponential has nonnegative entries. The same stochastic-matrix lemma can support discrete-time convergence results, powers of the matrix, and later examples. The generator-specific work is confined to constructing `R` and proving the displayed identities.

The definition of a stochastic matrix has two parts:
\[
  R(x,y)\geq0,\qquad \sum_yR(x,y)=1.
\]
From these, prove by induction on `n` that `R^n` is stochastic. Nonnegativity of a product entry follows from
\[
  (R^{n+1})(x,y)=\sum_zR^n(x,z)R(z,y),
\]
because every summand is nonnegative. For row sums, rearrange the finite sums and use the row-sum equation for the final factor:
\[
  \sum_y(R^{n+1})(x,y)
  =\sum_zR^n(x,z)\sum_yR(z,y)
  =\sum_zR^n(x,z)=1.
\]
Keep these induction results as lemmas about powers; later series arguments should not need to reopen the matrix multiplication proof.

## 3. The Poisson mixture

Set
\[
  w_n(t)=e^{-\Lambda t}\frac{(\Lambda t)^n}{n!}.
\]
For `t ≥ 0`, these weights are nonnegative and sum to one. Define each entry of `P_t` by
\[
  P_t(x,y)=\sum_{n=0}^{\infty}w_n(t)(R^n)(x,y).
\]
Since each summand is nonnegative, entrywise nonnegativity follows from closure of nonnegative reals under convergent sums. For row sums, interchange the finite sum over `y` with the nonnegative series over `n`:
\[
\begin{aligned}
  \sum_yP_t(x,y)
    &=\sum_y\sum_nw_n(t)(R^n)(x,y)\\
    &=\sum_nw_n(t)\sum_y(R^n)(x,y)\\
    &=\sum_nw_n(t)=1.
\end{aligned}
\]
The result is stochasticity of `P_t` with no matrix-exponential positivity theorem required.

There are two sensible Lean representations of this formula. One can define a matrix-valued sum using the `tsum` of scaled matrices, then obtain each entry by a continuity or evaluation lemma. Or one can define each entry as a scalar `tsum` and prove row-sum facts at the entry level. The matrix-valued form keeps the semigroup equation compact; the entrywise form makes nonnegativity and finite-state probability interpretation direct. A bridge lemma between them can prevent the choice from leaking into every theorem.

Infinite sums require more care than finite sums. Nonnegative terms support monotone and `ENNReal` arguments, while real-valued matrix entries require summability or a theorem identifying a convergent series. The Poisson weights sum to one, and each matrix entry `(R^n)(x,y)` lies in `[0,1]`; hence the weighted series is absolutely convergent and bounded by the sum of the weights. In Lean, this bound is often the cleanest way to establish summability before moving between real sums and finite row sums.

Do not use an unqualified rewrite to interchange `∑ y` and `∑' n`. State the finite index type, nonnegativity or summability hypotheses, and the exact interchange theorem. Such a lemma is mathematically routine but often the most delicate part of the implementation because sum APIs distinguish finite sums, `tsum`, `ℝ`, and `ℝ≥0∞`.

## 4. The matrix-exponential identity

The identity `Q=Λ(R-I)` gives
\[
  tQ=-\Lambda t I+\Lambda tR.
\]
The two matrices on the right commute: every matrix commutes with the identity. Therefore the exponential of the sum factors:
\[
  e^{tQ}=e^{-\Lambda t I}e^{\Lambda tR}.
\]
The power series for the second factor is
\[
  e^{\Lambda tR}
    =\sum_{n=0}^{\infty}\frac{(\Lambda t)^n}{n!}R^n,
\]
and the first factor is the scalar multiple `e^{-Λt}I`. Combining them gives the Poisson mixture.

This derivation identifies uniformization with the usual finite-dimensional transition semigroup. It also tells us which proof route to choose. If the project already has a robust matrix-exponential development, prove the identity and derive the mixture. If stochasticity is the main goal, define the transition matrix by the Poisson mixture first and prove the exponential identity as a characterization. In either route, the commuting-exponential theorem applies to the algebraic factorization; it does not establish that the resulting matrix has nonnegative entries.

The finite-dimensional setting matters. The matrix exponential is defined through a norm-convergent series, and multiplication by a fixed matrix is continuous. These analytic facts justify the series manipulations. In a formal development, avoid pretending that the exponential identity is a purely finite algebraic rewrite: the factorization uses a theorem about exponentials in a complete normed algebra. Mathlib documents matrix exponential identities, including the sum rule for commuting matrices. The remaining proof is to match the power-series coefficients and the chosen normalization of `R`.

At `t=0`, only the `n=0` term has positive weight, so `P₀=I`. Differentiating at zero gives `P'_0=Λ(R-I)=Q`. More generally, differentiating the matrix exponential gives the Kolmogorov equations from Chapter 55. If differentiating the mixture directly, justify termwise differentiation on bounded time intervals; the exponential-series route often makes this step shorter.

## 5. The semigroup law by Poisson convolution

Uniformization also proves the semigroup law without appealing first to the exponential. For `s,t ≥ 0`,
\[
  P_sP_t
  =\sum_{n,m\geq0}w_n(s)w_m(t)R^{n+m}.
\]
The equality uses `R^nR^m=R^{n+m}`. Group terms by `k=n+m`. The scalar coefficient of `R^k` is
\[
  \sum_{n=0}^{k}w_n(s)w_{k-n}(t).
\]
Substituting the weights and applying the binomial theorem gives
\[
  e^{-\Lambda(s+t)}\frac{(\Lambda(s+t))^k}{k!}=w_k(s+t).
\]
Therefore `P_sP_t=P_{s+t}`.

This argument expresses a probabilistic fact: the sum of independent Poisson counts with means `Λs` and `Λt` is Poisson with mean `Λ(s+t)`. It also exhibits exactly where the discrete-time semigroup powers are used. For a finite state space, the matrix product contributes only a finite sum over intermediate states; the two Poisson indices contribute a double infinite series. A Lean proof can first show the finite matrix identity, then handle the scalar convolution independently, and finally apply a summable-series rearrangement.

An alternative proof uses `P_t=e^{tQ}` and the exponential addition law for commuting scalar multiples of the same matrix. This is shorter once the exponential representation is established. The convolution proof is valuable when the mixture is the primary definition, and it provides an independent check that the probability construction has the expected time-homogeneous composition rule.

## 6. Clock interpretation and genuine jumps

Imagine a Poisson clock of rate `Λ`. At each ring, update the state according to `R`. When the current state is `x`, the probability of moving to a different state at a ring is
\[
  \sum_{y\ne x}R(x,y)=\frac{\lambda(x)}{\Lambda}.
\]
The candidate ring rate is `Λ`, so the rate of genuine departures from `x` is `Λ·λ(x)/Λ=λ(x)`. Conditional on a genuine departure, the destination distribution is
\[
  \frac{R(x,y)}{\sum_{z\ne x}R(x,z)}
  =\frac{q_{xy}}{\lambda(x)}
\]
when `λ(x)>0`. These are exactly the holding and jump rules associated to `Q`.

The clock can ring and leave the state unchanged. Those self-transitions are a bookkeeping device: they allow every state to share the same candidate event rate. Without them, each state would have a different waiting-time parameter, and a direct series over a fixed number of events would be harder to organize.

```text
candidate events N_t ~ Poisson(Λt)
state path:  x₀ ── R ──▶ x₁ ── R ──▶ ··· ── R ──▶ x_{N_t}
```

The horizontal steps are clock rings, and a step may leave the state unchanged. The endpoint after the random number of candidate events has transition matrix `P_t`.
This interpretation suggests an algorithm. To simulate the chain up to time `T`, sample a Poisson number `N` with mean `ΛT`, sample `N` transitions from `R`, and return the state after those transitions. The algorithm may perform redundant self-transitions, but it has the correct distribution. For a proof, specifying this sampling algorithm is distinct from proving the transition matrix formula: random-number generation, independence, and the law of the Poisson count each have their own interfaces.

At an absorbing state, `λ(x)=0`. Then `R(x,x)=1` and `R(x,y)=0` for `y≠x`, so every clock ring is a self-transition. This makes absorbing behavior automatic in the uniformized chain, rather than a special branch in the Poisson mixture.

## 7. Worked example: two states

Consider a chain with rates `a>0` from `0` to `1` and `b>0` from `1` to `0`. Set `Λ=a+b`, a convenient positive upper bound on both exit rates. Then
\[
  Q=\begin{pmatrix}-a&a\\b&-b\end{pmatrix},
  \qquad
  R=I+\frac{Q}{a+b}
   =\begin{pmatrix}
      \frac{b}{a+b}&\frac{a}{a+b}\\
      \frac{b}{a+b}&\frac{a}{a+b}
     \end{pmatrix}.
\]
Both rows of `R` equal the stationary distribution of the continuous-time chain. After one Poisson event, the current state has already been replaced by a stationary draw; further applications of `R` do nothing because `R²=R`.

Consequently,
\[
  P_t=e^{-(a+b)t}I+(1-e^{-(a+b)t})R.
\]
Indeed, the probability of zero clock rings is `e^{-(a+b)t}`, while the probability of one or more rings is the complementary term. Expanding the four entries recovers the transition formulas from Chapter 55. This example is unusually simple because the uniformized matrix is a projection. In larger chains, the powers `R^n` generally continue to evolve.

The example also illustrates a helpful formalization strategy. Prove `R²=R` directly from its rows, then simplify the whole series using `R^n=R` for `n>0`. This gives an exact solution without diagonalizing the generator. It is an example-specific proof, whereas the uniformization theorem applies to every finite generator satisfying the same rate bound.

## 8. Stationarity and reversibility transfer

Let `π` be a probability row vector. Since
\[
  Q=\Lambda(R-I),
\]
the equation `πQ=0` is equivalent to `πR=π`, because `Λ>0`. If `πR=π`, induction gives `πR^n=π` for every natural number `n`. Then
\[
  \pi P_t
    =\sum_nw_n(t)\pi R^n
    =\sum_nw_n(t)\pi
    =\pi.
\]
Thus generator stationarity transfers to every time in the continuous-time semigroup through a discrete invariance lemma and the fact that Poisson weights sum to one.

Rate detailed balance transfers as well. For `x ≠ y`,
\[
  \pi(x)R(x,y)=\frac{\pi(x)q_{xy}}{\Lambda}
              =\frac{\pi(y)q_{yx}}{\Lambda}
              =\pi(y)R(y,x).
\]
On the diagonal the equality is tautological. Therefore the one-step matrix `R` is reversible with respect to `π`. Powers of a reversible kernel remain reversible with respect to the same law, and a nonnegative mixture of such powers also preserves the detailed-balance equation. This gives a second route to reversibility of `P_t`.

Be precise about the theorem used for powers. Invariance is preserved by composition directly. Reversibility of a composition is not a general fact for two unrelated kernels; here it holds because both factors are powers of the same reversible operator. A formal proof should either establish the power theorem by induction using the weighted inner-product characterization, or use self-adjointness of the operator on the appropriate `L²(π)` space.

## 9. Lean development architecture

A reusable development can divide the argument into four layers:

1. **Generator data:** finite state space, off-diagonal rates, row sums, and an upper bound `Λ`.
2. **Discrete kernel:** construction of `R` and proof that it is stochastic.
3. **Series family:** definition of Poisson weights and the matrix mixture, with summability and stochasticity.
4. **Dynamics:** semigroup, derivative, generator identification, stationarity, and optional process construction.

One possible starting interface is:

```lean
def IsStochastic {S : Type*} [Fintype S] (P : Matrix S S ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧
  (∀ x, ∑ y, P x y = 1)

structure Generator (S : Type*) [Fintype S] where
  rate : Matrix S S ℝ
  offDiag_nonneg : ∀ x y, x ≠ y → 0 ≤ rate x y
  row_sum_zero : ∀ x, ∑ y, rate x y = 0
```

This sketch intentionally leaves the type-class assumptions and representation of rates visible. A production API may require `[DecidableEq S]` for the chosen finite-sum notation and may bundle the upper bound separately. Avoid building a large structure before learning which fields downstream theorems actually need; conversely, once several chapters share these hypotheses, a named structure prevents long lists of near-identical arguments.

The central lemmas should have stable, mathematical names even if the implementation uses a different representation:

- `uniformizedMatrix_nonneg`;
- `uniformizedMatrix_row_sum`;
- `uniformizedPower_isStochastic`;
- `poissonWeights_sum`;
- `uniformizedSemigroup_isStochastic`;
- `uniformizedSemigroup_comp`;
- `uniformizedSemigroup_derivative_zero`.

These names are suggestions, not claims about existing Mathlib declarations. Search the current library before creating aliases, and distinguish your textbook development from upstream APIs. Mathlib documents finite matrix exponential identities, exponential distributions, kernel composition, and the Chapman–Kolmogorov equation for kernel powers. These are useful components, but they should not be mistaken for a turnkey theorem that a chosen finite generator's exponential is already a Markov semigroup.

If the next theorem concerns only a finite transition probability, matrix-level proofs may be enough. To connect the result to general measurable kernels, define the finite-state kernel and show that its composition corresponds to matrix multiplication. For stopping times, adaptedness, or paths, construct the process and filtration only after the semigroup layer is stable. This mirrors the separation in Chapter 55 between a generator, a family of transition matrices, and a process-level model.

## 10. Exercises

1. Prove that the bound `Λ ≥ max_x λ(x)` makes every diagonal entry of `R` nonnegative.
2. Show that `R` has row sums one using only the generator row-sum equation.
3. Prove by induction that a stochastic matrix has stochastic natural powers.
4. Establish that the Poisson weights are nonnegative and sum to one.
5. Give an absolute-convergence bound for each entry of the Poisson mixture.
6. Prove the semigroup law by grouping the double sum according to `n+m`.
7. Derive the matrix-exponential identity from `Q=Λ(R-I)` and commuting exponentials.
8. Explain why self-transitions do not alter the genuine jump rates.
9. Show that `πQ=0` is equivalent to `πR=π` when `Λ>0`.
10. Prove that rate detailed balance for `Q` implies detailed balance for `R`.
11. For the two-state example, verify `R²=R` and derive `P_t=e^{-Λt}I+(1-e^{-Λt})R`.
12. Identify which steps of a Lean proof require finite sums, which require `tsum`, and which require a differential equation theorem.

## Summary

Uniformization chooses one rate `Λ` that bounds every exit rate and forms the stochastic matrix `R=I+Q/Λ`. The continuous-time transition matrix is the Poisson-weighted sum of powers of `R`. Nonnegativity and row normalization follow term by term, while the matrix exponential identity and Poisson convolution establish the standard semigroup dynamics. Stationarity and detailed balance transfer from the generator to the uniformized kernel. In formalization, keep finite matrix arguments, infinite-series convergence, and process construction as separate proof layers.

## Further reading

- [Mathlib: Matrix exponential](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/MatrixExponential.html)
- [Mathlib: Exponential distributions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Exponential.html)
- [Mathlib: Markov kernel composition and Chapman–Kolmogorov](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html)
- Chapter 48 for quantitative convergence of finite Markov chains.
- Chapters 55–56 for continuous-time generators and their uniformized semigroups.

