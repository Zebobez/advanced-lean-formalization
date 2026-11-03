# Chapter 55 — Finite-State Continuous-Time Markov Chains

> **Audience.** This chapter assumes familiarity with finite Markov chains, matrix multiplication, derivatives, and probability measures. It introduces finite-state continuous-time chains through their rate matrices and transition semigroups.

A discrete-time Markov chain makes one transition at each integer step. A continuous-time chain can jump at irregular times, and its transition law depends on elapsed time. On a finite state space, the dynamics are encoded by a generator matrix: off-diagonal entries give jump rates, and diagonal entries make every row sum to zero. The transition matrices form a semigroup and solve the Kolmogorov differential equations.

This chapter develops the finite-state mathematics and its formal proof boundaries. Mathlib provides matrix exponentials, the ordinary exponential distribution, kernel composition, and filtrations, but this presentation builds the finite generator and transition semigroup directly from those pieces. A matrix exponential is an algebraic construction; proving its entries are nonnegative and each row sums to one is a separate stochastic argument.

## Learning objectives

By the end of the chapter, you should be able to:

- define a finite-state generator matrix from transition rates;
- interpret diagonal entries as negative exit rates;
- derive the small-time transition expansion;
- characterize stationary distributions by `πQ=0`;
- write the forward and backward equations with a consistent matrix convention;
- separate matrix-exponential identities from probability-kernel properties.

## 1. Rate matrices

Let `S` be a finite state type. A generator is a matrix `Q : Matrix S S ℝ` satisfying

\[
  q_{xy}\geq0\quad(x\ne y),
  \qquad
  q_{xx}=-\sum_{y\ne x}q_{xy}.
\]

The exit rate from `x` is

\[
  \lambda(x)=\sum_{y\ne x}q_{xy}=-q_{xx}.
\]

The row-sum identity `∑_y q_{xy}=0` follows. Off-diagonal entries are rates, not transition probabilities: they can exceed one and have units of inverse time. The diagonal is nonpositive and records the total rate of leaving the state.

When the process is at `x` with `λ(x)>0`, its holding time is exponentially distributed with rate `λ(x)`. After the holding time, it jumps to `y≠x` with probability `q_{xy}/λ(x)`. A state with exit rate zero is absorbing. This jump description and the rate-matrix description encode the same finite-state dynamics, but the semigroup formulation is often easier to use in algebraic proofs.

## 2. The small-time transition law

Let `P_t(x,y)` be the probability of being in state `y` after elapsed time `t`, starting from `x`. For small positive `h`,

\[
  P_h(x,y)=q_{xy}h+o(h)\quad(x\ne y),
\]

and

\[
  P_h(x,x)=1+q_{xx}h+o(h)=1-\lambda(x)h+o(h).
\]

The probability of one jump from `x` to `y` is approximately its rate times the short interval length. The probability of two or more jumps contributes only a higher-order term in a finite-rate system.

In matrix form, using row distributions and matrices whose rows index source states,

\[
  P_h=I+hQ+o(h).
\]

This is the definition of the generator as the derivative of the transition semigroup at zero. In a formal proof, the derivative is taken entrywise or in a matrix norm; finite dimensionality lets these viewpoints agree. The nonnegative off-diagonal rate and zero row sums are the hypotheses that make `Q` a stochastic generator rather than an arbitrary matrix.

## 3. Transition semigroups

The Markov property and time-homogeneity imply the semigroup identity

\[
  P_{s+t}=P_sP_t,\qquad P_0=I.
\]

Each `P_t` is a stochastic matrix: its entries are nonnegative and each row sums to one. If distributions are row vectors, an initial law evolves as `μ_t=μ_0P_t`.

```text
initial law μ₀  ── P_s ──▶  law μ_s  ── P_t ──▶  law μ_{s+t}
                 composition: P_s P_t = P_{s+t}
```

For a finite generator, the candidate transition matrix is the matrix exponential

\[
  P_t=e^{tQ}.
\]

The algebraic exponential satisfies `P_0=I`, the semigroup identity, and the differential equation `P_t'=P_tQ=QP_t`. It also has derivative `Q` at zero. These facts identify the candidate solution of the Kolmogorov equations. They do not by themselves show that `P_t` is stochastic; nonnegativity of an exponential of a matrix with nonnegative off-diagonals needs a separate argument, such as uniformization in Chapter 56.

Mathlib's matrix-exponential API supports exponentials over finite matrix types and identities for sums of commuting matrices. The finite matrix type is complete under its standard normed-algebra structure. Once the semigroup formula is represented, the remaining formal work is to establish the generator hypotheses and connect the matrix rows to finite probability measures.

## 4. Forward and backward equations

Under the row-vector convention, the forward equation is

\[
  \frac{d}{dt}P_t=P_tQ.
\]

It describes how probability mass flows out of each current state and into other states. If `u_t` is an initial row distribution evolved as `u_t=u_0P_t`, then `u_t'=u_tQ`.

The backward equation is

\[
  \frac{d}{dt}P_t=QP_t.
\]

For a time-homogeneous finite generator, both equations hold because `Q` commutes with its exponential. The forward equation differentiates with respect to the terminal distribution; the backward equation differentiates with respect to the starting state. In nonhomogeneous models or alternative matrix conventions, the two equations can have different time arguments or placement of the generator.

On observables viewed as column vectors, the transition operator acts by `P_t f`. The generator acts as

\[
  (Qf)(x)=\sum_yq_{xy}f(y)
        =\sum_{y\ne x}q_{xy}(f(y)-f(x)).
\]

The second expression shows that constants lie in the kernel of `Q`. It is often the best representation for proofs about expected observables and martingales.

## 5. Stationary distributions and generator balance

A probability row vector `π` is stationary if

\[
  \pi P_t=\pi\quad\text{for all }t\geq0.
\]

If `πQ=0`, then

\[
  \pi e^{tQ}=\pi,
\]

because every positive power of `Q` annihilates `π`. Conversely, differentiating stationarity at zero gives `πQ=0`. Thus the stationary equations for the semigroup reduce to a finite linear system, together with nonnegativity and total mass one.

Detailed balance for rates is the pairwise condition

\[
  \pi(x)q_{xy}=\pi(y)q_{yx}\quad(x\ne y).
\]

Summing over destinations shows `πQ=0`: the incoming and outgoing weighted rates cancel. This is the continuous-time analogue of reversibility for a transition kernel. It is stronger than stationarity, just as in Chapter 45.

If detailed balance holds, then `π` is stationary for every transition matrix `P_t`. One way to prove this is through the generator equation; another is through uniformization, where the discrete transition matrix inherits detailed balance. Use the route that matches the available formal interface.

## 6. Worked example: a two-state chain

Let the jump rate from `0` to `1` be `a>0` and the jump rate from `1` to `0` be `b>0`. Then

\[
  Q=\begin{pmatrix}-a&a\\b&-b\end{pmatrix}.
\]

The stationary distribution solves `πQ=0` and is

\[
  \pi(0)=\frac{b}{a+b},\qquad
  \pi(1)=\frac{a}{a+b}.
\]

The transition probabilities are

\[
\begin{aligned}
  P_t(0,1)&=\frac{a}{a+b}(1-e^{-(a+b)t}),\\
  P_t(1,0)&=\frac{b}{a+b}(1-e^{-(a+b)t}),\\
  P_t(0,0)&=\frac{b}{a+b}+\frac{a}{a+b}e^{-(a+b)t},\\
  P_t(1,1)&=\frac{a}{a+b}+\frac{b}{a+b}e^{-(a+b)t}.
\end{aligned}
\]

At `t=0` these entries form the identity; as `t→∞`, both rows converge to the stationary law. The generator detailed-balance equation is `π(0)a=π(1)b`.

This example admits two formal proofs. One computes the matrix exponential by diagonalizing `Q` or splitting it into the projection onto constants and the decaying centered component. The other solves the two scalar forward equations. The latter is often easier to audit, while the matrix method scales better when spectral structure is available.

### Example: a directed three-cycle

Let the states be `0,1,2`, with a jump of rate `c>0` from `0` to `1`,
from `1` to `2`, and from `2` to `0`. The generator is
\[
  Q=\begin{pmatrix}
    -c&c&0\\
    0&-c&c\\
    c&0&-c
  \end{pmatrix}.
\]
Every row sums to zero, and the uniform distribution
`π=(1/3,1/3,1/3)` satisfies `πQ=0`: each state receives rate `c/3` and
sends rate `c/3`. Yet the chain is not reversible. For example,
`π(0)q_{01}=c/3` while `π(1)q_{10}=0`.

This small model separates stationarity from detailed balance more clearly
than the two-state chain, where global balance forces the two opposing
weighted rates to match. A Lean proof can encode the matrix by a three-by-three
table and discharge the finite row sums and stationary equations by
normalization. The mathematical lesson is broader than this example:
circulating probability flow can preserve a law without balancing each edge
individually.

## 7. Generator construction from jump rates

Suppose rates are given only for distinct states. Define the diagonal by the negative sum of outgoing rates. This makes the row-sum-zero property definitional and leaves one main obligation: off-diagonal nonnegativity.

In Lean, a finite generator can be a matrix with a predicate recording those two conditions, or a structure bundling the matrix with proofs. The bundled form is useful if many theorems use the same generator; a local matrix plus named hypotheses is simpler for one-off examples. State the source/target matrix orientation in the type or documentation so multiplication by row distributions is not silently reversed.

For `S=Fin n`, `Matrix.mul_apply` reduces matrix products to finite sums. Keep the identity `∑_y Q(x,y)=0` as a lemma. It is used repeatedly in proofs that constants are annihilated, that the derivative of row mass is zero, and that a stationary vector remains normalized.

## 8. Filtrations and process-level statements

A transition semigroup specifies finite-dimensional conditional distributions, but a stochastic process also has a sample space, a filtration, and pathwise measurability properties. Mathlib's filtration and stochastic-process interfaces can express information available over continuous time, including an `ℝ≥0`-indexed right-continuous filtration. They do not eliminate the need to construct the process or prove its Markov property.

For finite-state examples, one can first work entirely at the semigroup level: prove transition probabilities, composition, and stationary laws. Only when a result concerns stopping times, adaptedness, or pathwise sample paths should the development introduce a process and filtration. This staged approach avoids building a path-space probability measure when the theorem only uses one-time transition matrices.

### The path-space boundary

The Chapman–Kolmogorov identity is the consistency condition behind
finite-dimensional distributions at several time points. It lets a proof
compute a joint law by composing transition kernels in chronological order.
That calculation is still a statement about a finite list of observations;
it does not, on its own, supply a sample path defined at every real time.

For a finite-state chain, a pathwise construction can use an initial state,
a sequence of holding times, and a sequence of destination choices. One
then proves that the construction has only finitely many genuine jumps on
each bounded interval. A bounded exit rate gives a useful route: compare
the number of genuine jumps with the number of rings of a dominating Poisson
clock. Chapter 56 develops that uniformization argument. This domination
also explains why finite-state bounded-rate chains do not explode in finite
time.

The distinction matters when designing a Lean theorem. If the desired result
is an expectation at a fixed time, a transition matrix may be the complete
object. If the result quantifies over all times along a path, mentions a
stopping time, or asks for right-continuous trajectories, the process
construction and measurability proofs become part of the theorem's
hypotheses and conclusion. Keeping this boundary visible prevents a
semigroup proof from silently claiming pathwise regularity it has not
established.

## 9. From algebraic identities to probability

Two matrix properties are especially easy to conflate. The identity
`P_t \mathbf 1=\mathbf 1` says that each row sums to one. Entrywise
nonnegativity says that each row assigns nonnegative mass to every state.
Together they make a finite stochastic matrix. Either property alone is
insufficient: a row can sum to one while containing negative entries.

For the exponential candidate, row sums follow directly from
`Q \mathbf 1=0`. Every positive power of `Q` also annihilates
` \mathbf 1`, so the power series for `e^{tQ}` leaves ` \mathbf 1`
fixed. In Lean this argument can be organized as a lemma about powers
followed by a continuity argument for the exponential series, or avoided by
defining the transition family through uniformization in the next chapter.
The second route packages row-sum preservation into discrete matrix powers.

Positivity has a different shape. It does not follow from `Q` being a
nonnegative matrix because its diagonal entries are usually negative. The
relevant condition is that only the off-diagonal entries are nonnegative.
Uniformization rewrites the exponential using a stochastic matrix and
nonnegative scalar coefficients, making entrywise positivity visible term by
term. This distinction is useful in proof design: prove the algebraic
semigroup identities where they are simplest, and prove stochasticity with an
argument that uses the sign pattern.

Uniqueness is a third claim. If two matrix-valued differentiable functions
have the same initial value and solve the same constant-coefficient
differential equation, a standard uniqueness theorem identifies them. That
justifies identifying an independently constructed transition family with
`e^{tQ}`. It is a separate obligation from showing either family is
stochastic. In a textbook formalization, state the ODE, initial condition,
and uniqueness result explicitly rather than using the word “solution” to
hide all three facts.

## 10. Encoding a generator for reusable proofs

There are two natural encodings. The first starts with a matrix `Q` and a
predicate expressing off-diagonal nonnegativity and zero row sums. It is
convenient when existing matrix lemmas are the main interface. The second
starts with rates `r : S → S → ℝ` and defines the diagonal from the sum of
the outgoing rates. It makes the generator laws automatic but requires a
conversion lemma before using matrix-exponential results.

For the rate-based representation, define a separate exit-rate function
\[
  \lambda(x)=\sum_{y\ne x}r(x,y)
\]
and set
\[
  Q(x,y)=
  \begin{cases}
    -\lambda(x),&x=y,\\
    r(x,y),&x\ne y.
  \end{cases}
\]
Assume `r(x,y) ≥ 0` for `x ≠ y`. Then a finite-sum argument proves the row
sum is zero. Keeping `λ` as a named definition avoids repeatedly unfolding a
conditional and helps state holding-time results. If a data structure
bundles `Q`, `λ`, and proofs relating them, expose accessors for the facts
used by downstream chapters instead of making later proofs unfold the entire
structure.

Finite sums introduce practical obligations. A sum over all `y` with a
conditional test `y ≠ x` is often easier to rewrite with a sum over the
subtype `{y // y ≠ x}`. The subtype form makes the exclusion explicit but
adds coercions; the conditional form works directly with `Finset.univ` and a
decidable equality. Choose one as the primary definition and prove a named
equivalence lemma if both styles are useful.

Matrix orientation should be recorded once. Here `Q x y` means the rate from
source `x` to destination `y`, and probability distributions multiply on
the left. This convention yields `μ' = μQ`. A column-vector convention is
equally valid, but reverses the order of indices or uses a transpose. Small
examples are an effective audit: the two-state generator should send mass
out of state `0` at rate `a` and into state `1` at the same rate.

## 11. A proof workflow

1. Fix the convention for row distributions and source-indexed matrix rows.
2. Define off-diagonal rates and diagonal exit rates.
3. Prove nonnegative off-diagonal entries and zero row sums.
4. Define the candidate matrix exponential or a uniformized transition family.
5. Prove the semigroup and differential identities.
6. Establish stochasticity by a positivity argument, not from the exponential notation alone.
7. Solve `πQ=0` or prove rate detailed balance.
8. Connect finite matrices to kernels only when measurable-space results are needed.
9. Introduce a process and filtration only for pathwise or stopping-time claims.

## 12. Common failure modes

### Rates are treated as probabilities

Off-diagonal generator entries are nonnegative rates and need not be at most one.

### The diagonal is chosen independently of the outgoing rates

The row-sum-zero identity determines the diagonal.

### A matrix exponential is assumed stochastic

The exponential identities do not automatically prove entrywise nonnegativity.

### The forward equation uses the wrong multiplication order

Declare whether distributions are row vectors and use that convention consistently.

### Generator stationarity is confused with reversibility

`πQ=0` is global balance; pairwise detailed balance is stronger.

### A semigroup is confused with a process construction

Transition matrices alone do not establish sample paths, adaptedness, or stopping-time results.

## 13. Exercises

1. Define a generator matrix from finite off-diagonal rates.
2. Prove every row of the generator sums to zero.
3. Derive the small-time expansion `P_h=I+hQ+o(h)`.
4. State the forward and backward equations under the row-vector convention.
5. Prove that `πQ=0` implies `πe^{tQ}=π`.
6. Show that rate detailed balance implies the generator stationary equations.
7. Compute the stationary law for the two-state chain.
8. Derive the two-state transition probabilities from the forward equations.
9. Explain why the matrix exponential's semigroup property does not alone prove stochasticity.
10. Locate the matrix-exponential and exponential-distribution interfaces in Mathlib's documentation.

## Summary

A finite-state continuous-time Markov chain is encoded by a generator with nonnegative off-diagonal rates and zero row sums. Its transition semigroup solves Kolmogorov equations and is represented by a matrix exponential. Stationarity is characterized by `πQ=0`, while rate detailed balance is a stronger symmetric-flow condition. Formal proofs must keep the generator algebra, stochasticity of the semigroup, and any path-space process construction as distinct layers.

## Further reading

- [Mathlib: Matrix exponential](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/MatrixExponential.html)
- [Mathlib: Exponential waiting-time distribution](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Exponential.html)
- [Mathlib: Filtrations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Filtration.html)
- Chapters 45 and 55 for invariance, detailed balance, and continuous-time generators.

## 14. Lean formalization

The first block keeps the repository's original two-state integer generator
check. The following blocks make the chapter's finite-state claims executable:
they prove row conservation for a symbolic two-state generator, normalize its
stationary law and verify `πQ=0`, then check a directed three-cycle whose
uniform law is stationary although one-way edge flows violate detailed
balance. The examples formalize finite algebraic statements; identifying a
transition semigroup with a matrix exponential and proving its stochasticity
remain separate analytic tasks.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

theorem generatorConservesMassAtZero : generatorRowSum twoStateGenerator zero = 0 :=
  generator_zero_row
theorem generatorConservesMassAtOne : generatorRowSum twoStateGenerator one = 0 :=
  generator_one_row
```

For symbolic jump rates `a` and `b`, the diagonal entries are their negative
exit rates. The following functions use source states as the first argument
and destination states as the second.

```lean
def rationalTwoStateGenerator (a b : ℚ) (i j : State) : ℚ :=
  if i = zero then (if j = zero then -a else a)
  else if j = zero then b else -b

def rationalTwoStateRowSum (a b : ℚ) (i : State) : ℚ :=
  rationalTwoStateGenerator a b i zero + rationalTwoStateGenerator a b i one

def rationalTwoStateStationary (a b : ℚ) (i : State) : ℚ :=
  if i = zero then b / (a + b) else a / (a + b)

def rationalTwoStateStationaryAction (a b : ℚ) (j : State) : ℚ :=
  rationalTwoStateStationary a b zero * rationalTwoStateGenerator a b zero j +
    rationalTwoStateStationary a b one * rationalTwoStateGenerator a b one j

theorem rational_two_state_generator_row_sum (a b : ℚ) (i : State) :
    rationalTwoStateRowSum a b i = 0 := by
  fin_cases i <;>
    simp [rationalTwoStateRowSum, rationalTwoStateGenerator, zero, one]

theorem rational_two_state_stationary_normalized (a b : ℚ) (h : a + b ≠ 0) :
    rationalTwoStateStationary a b zero + rationalTwoStateStationary a b one = 1 := by
  simp [rationalTwoStateStationary, zero, one]
  field_simp [h]
  exact add_comm b a

theorem rational_two_state_stationary_equation (a b : ℚ) (h : a + b ≠ 0)
    (j : State) : rationalTwoStateStationaryAction a b j = 0 := by
  fin_cases j <;>
    simp [rationalTwoStateStationaryAction, rationalTwoStateStationary,
      rationalTwoStateGenerator, zero, one] <;>
    field_simp [h] <;> ring
```

The directed cycle below has rate `c` from each state to its successor. Its
row sums and column sums vanish, so the uniform distribution is stationary.
The reverse rate on each directed edge is zero, demonstrating that stationarity
does not imply detailed balance.

```lean
def threeCycleGenerator (c : ℚ) (i j : Fin 3) : ℚ :=
  if i = 0 then (if j = 0 then -c else if j = 1 then c else 0)
  else if i = 1 then (if j = 1 then -c else if j = 2 then c else 0)
  else if j = 0 then c else if j = 2 then -c else 0

def threeCycleRowSum (c : ℚ) (i : Fin 3) : ℚ :=
  threeCycleGenerator c i 0 + threeCycleGenerator c i 1 + threeCycleGenerator c i 2

def threeCycleColumnSum (c : ℚ) (j : Fin 3) : ℚ :=
  threeCycleGenerator c 0 j + threeCycleGenerator c 1 j + threeCycleGenerator c 2 j

theorem three_cycle_rows_sum_to_zero (c : ℚ) (i : Fin 3) :
    threeCycleRowSum c i = 0 := by
  fin_cases i <;> simp [threeCycleRowSum, threeCycleGenerator]

theorem three_cycle_uniform_stationary (c : ℚ) (j : Fin 3) :
    (1 / 3 : ℚ) * threeCycleGenerator c 0 j +
      (1 / 3 : ℚ) * threeCycleGenerator c 1 j +
      (1 / 3 : ℚ) * threeCycleGenerator c 2 j = 0 := by
  fin_cases j <;> simp [threeCycleGenerator]

theorem three_cycle_uniform_mass :
    (1 / 3 : ℚ) + 1 / 3 + 1 / 3 = 1 := by norm_num

theorem three_cycle_edge_flows_differ (c : ℚ) (hc : 0 < c) :
    (1 / 3 : ℚ) * threeCycleGenerator c 0 1 ≠
      (1 / 3 : ℚ) * threeCycleGenerator c 1 0 := by
  simp [threeCycleGenerator]
  positivity
```

