# Chapter 63 — Birth–Death Chains and Hitting Problems

> **Audience.** This chapter assumes familiarity with finite-state generators, reversibility, stopping times, and linear systems. It studies chains whose transitions move only to neighboring states.

Birth–death chains are one-dimensional continuous-time Markov chains with local motion. From state i, the process can move only to i+1 or i−1. This simple geometry turns stationary equations, hitting probabilities, and expected absorption times into recurrences. Those recurrences are useful both mathematically and formally: a large matrix theorem can often be reduced to a short induction over adjacent states.

This chapter works first on a finite interval, where all rates are bounded and non-explosion is automatic. The same formulas motivate infinite-state birth–death processes, but boundary behavior and recurrence require extra analysis there.

## Learning objectives

By the end of the chapter, you should be able to:

- encode a finite birth–death chain as a generator with nearest-neighbor rates;
- derive its stationary law from adjacent detailed-balance equations;
- solve a two-boundary hitting-probability problem by differences;
- compute expected absorption times from a Poisson equation;
- interpret reversibility through conductances on a path graph;
- organize boundary cases and finite recurrences in Lean.

## 1. The nearest-neighbor generator

Take the state space \(\{0,1,\ldots,N\}\), with N≥1. From state i, let λ_i be the rate to i+1 and μ_i the rate to i−1. At the boundaries put λ_N=0 and μ_0=0. All rates are nonnegative; an interior state can be absorbing if both rates vanish.

For a function f on the state space, the generator is
\[
  (Qf)(i)
   =\lambda_i\bigl(f(i+1)-f(i)\bigr)
    +\mu_i\bigl(f(i-1)-f(i)\bigr),
\]
where a term is omitted when the corresponding neighbor does not exist. Equivalently, Q(i,i+1)=λ_i, Q(i,i−1)=μ_i, and the diagonal is the negative sum of the available outgoing rates.

The local formula makes Qf(i) the upward contribution plus the downward contribution. It is generally clearer than defining every matrix entry separately, because the row-sum-zero property is built into each difference. To use matrix APIs, define Q from the rates and prove a lemma that its action on f agrees with this formula.

For a finite interval, the total exit rate is at most \(\max_i(\lambda_i+\mu_i)\), so Chapter 56’s uniformization applies. The chain cannot make infinitely many genuine jumps in finite time.

## 2. Stationary weights from edge balance

Assume λ_i>0 for i<N and μ_i>0 for i>0. Then every neighboring pair communicates in both directions, so the finite chain is irreducible. Detailed balance across the edge {i,i+1} requires
\[
  \pi_i\lambda_i=\pi_{i+1}\mu_{i+1}.
\]
Set w_0=1 and define recursively
\[
  w_{i+1}=w_i\frac{\lambda_i}{\mu_{i+1}}.
\]
Every weight is positive. Normalize by \(Z=\sum_{i=0}^Nw_i\) and put \(\pi_i=w_i/Z\). The adjacent detailed-balance equations hold by construction, while non-neighboring rates are zero in both directions. Therefore π is reversible and stationary.

This recursive construction is more efficient than solving all N+1 stationary equations at once. The first-order edge relations determine every weight from w_0; normalization fixes the remaining scale. In Lean, define weights by recursion, prove positivity and the edge identity by induction, then normalize in a separate step.

For any finite birth–death chain that is not irreducible, the recursion may encounter a zero denominator or disconnected components. Do not state the positive formula without the positivity hypotheses. Reducible chains can have several stationary laws, one supported on each closed class.

## 3. Worked example: a finite-capacity queue

Consider a queue with capacity N. Arrivals occur at constant rate α when the queue is not full, and service completions occur at rate β when the queue is nonempty. Thus
\[
  \lambda_i=\alpha\quad(i<N),\qquad
  \mu_i=\beta\quad(i>0).
\]
Let ρ=α/β. The recursive weights are w_i=ρ^i, and the stationary distribution is
\[
  \pi_i=
  \begin{cases}
    \dfrac{1-\rho}{1-\rho^{N+1}}\rho^i,&\rho\ne1,\\[6pt]
    \dfrac1{N+1},&\rho=1.
  \end{cases}
\]
When ρ>1, both numerator and denominator in the first expression are negative, so the probabilities remain positive. The case ρ=1 is the continuous algebraic limit but should be handled separately in a proof to avoid division by zero.

The boundary rates encode the finite buffer: arrivals at capacity are suppressed, and service attempts at the empty state do not create a negative queue length. The stationary weights reveal how congestion changes with α/β. When arrivals outpace service, mass concentrates near capacity; when service is faster, low queue lengths receive more mass.

This model is a useful formalization exercise because the stationary law has a closed form and the detailed-balance proof is local. The normalizing sum is a finite geometric series. One can first prove the formula for the weights and only then show their sum is one.

## 4. Hitting probabilities as a difference equation

Let τ be the first time the chain hits either endpoint 0 or N. Define
\[
  h_i=\Pr_i(X_\tau=N).
\]
The boundary values are h_0=0 and h_N=1. At an interior state, conditioning on the first jump or using the stopped generator equation gives
\[
  (Qh)(i)=0,\qquad 1\leq i<N.
\]
Define increments d_i=h_i−h_{i−1} for 1≤i≤N. Then the harmonic equation becomes
\[
  \lambda_i d_{i+1}=\mu_i d_i.
\]
Let r_1=1 and recursively set
\[
  r_{k+1}=r_k\frac{\mu_k}{\lambda_k}
\]
for 1≤k<N. All increments are proportional to these r_k, and the boundary condition \(\sum_{k=1}^Nd_k=1\) gives
\[
  h_i=\frac{\sum_{k=1}^i r_k}{\sum_{k=1}^N r_k}.
\]
This formula makes the bias visible: if downward rates dominate along the path, the increments and therefore the chance of reaching N are reduced.

The proof can be split cleanly. First show the recurrence for d_i. Then prove by induction that d_i=d_1r_i. Finally, sum the differences to recover h_i and impose h_N=1. This proof structure avoids solving an N−1 by N−1 matrix system.

## 5. Worked example: the symmetric random walk

Let λ_i=μ_i=c>0 at each interior state. Then r_i=1, so
\[
  h_i=\frac{i}{N}.
\]
The probability of reaching N before 0 is linear in the starting state. A direct check gives
\[
  (Qh)(i)=c\left(\frac{i+1}{N}-\frac{i}{N}\right)
          +c\left(\frac{i-1}{N}-\frac{i}{N}\right)=0.
\]
The boundary values are correct, and uniqueness of the finite Dirichlet problem identifies h with the hitting probability.

The uniqueness proof is another useful formal lemma. If a function g is harmonic in the interior and vanishes at both endpoints, then a maximum or minimum principle forces g to vanish everywhere. Alternatively, use the finite linear system and show its kernel is trivial under the boundary constraints.

## 6. Expected absorption times

For the same stopping time τ, define \(u_i=\mathbb E_i[\tau]\), assuming τ is almost surely finite. Dynkin’s formula suggests the Poisson equation
\[
  (Qu)(i)=-1\quad(1\leq i<N),\qquad u_0=u_N=0.
\]
Indeed, stopping at τ∧T gives
\[
  \mathbb E_i[u(X_{\tau\wedge T})]
   =u_i-\mathbb E_i[\tau\wedge T].
\]
If τ is finite almost surely, the left side tends to zero as T→∞ because u is bounded on the finite state space. Monotone convergence then yields u_i=\(\mathbb E_i[\tau]\).

For the symmetric walk with rate c in each direction, the solution is
\[
  u_i=\frac{i(N-i)}{2c}.
\]
The second difference of the quadratic is −1/c, so Q u=−1 in the interior. The boundary values vanish. This gives a closed expected absorption time without summing the distribution of τ.

The limiting argument has real content. A bounded state space makes u(X_t) bounded, but it does not make τ bounded. Prove almost-sure absorption first, for example by a uniform positive probability of reaching a boundary during a fixed time interval from any interior state. Repeating that estimate gives a geometric tail over successive intervals.

## 7. Conductances and the path-graph energy

For a reversible birth–death chain, define the conductance of edge {i,i+1} by
\[
  c_i=\pi_i\lambda_i=\pi_{i+1}\mu_{i+1}.
\]
The Dirichlet form from Chapter 60 reduces to
\[
  \mathcal E(f,f)
    =\sum_{i=0}^{N-1}c_i\bigl(f(i+1)-f(i)\bigr)^2.
\]
Each undirected edge appears once. The stationary mass describes how often the chain occupies vertices; the conductance describes how much flow crosses each edge.

This formula connects stationary distributions, hitting probabilities, and spectral gaps. A low-conductance edge can bottleneck the path: functions that are nearly constant on either side but change across that edge have small energy. The Poincaré inequality then predicts slow mixing. On a one-dimensional state space, all of these questions can be expressed through finite sums of edge weights.

## 8. Formalization architecture

On the Lean side, a convenient state type is Fin (N+1). Define upward and downward rate functions with boundary values zero, then define the generator by cases on whether a neighbor exists. Keep the recurrence equations for stationary weights, harmonic functions, and expected times as separate definitions rather than unfolding them in every proof.

Useful reusable lemmas include:

1. the generator action formula for an arbitrary observable;
2. the zero row-sum equation;
3. the adjacent detailed-balance identity;
4. positivity and normalization of recursively defined stationary weights;
5. the first-difference recurrence for harmonic functions;
6. uniqueness for the finite Dirichlet and Poisson problems.

Boundary indices are the main source of elaboration work. In Fin notation, the predecessor of state zero and successor of state N do not exist. A clean approach proves interior recurrence lemmas under explicit bounds and handles endpoints separately. Avoid introducing wrapped modular arithmetic, which would silently connect N back to 0 and change the chain into a cycle.

For hitting times, first formalize the algebraic solution to Qh=0 or Qu=−1. Then connect it to the stochastic process with Dynkin’s formula and optional sampling. This separates finite recurrence proofs from the probability argument and makes it easier to reuse the same linear solution for multiple initial states.

## 9. Common failure modes

### Boundary rates are left implicit

State explicitly that λ_N=0 and μ_0=0, or omit unavailable neighbor terms.

### Rates are confused with jump probabilities

Normalize by the total exit rate to obtain the embedded jump chain.

### A stationary formula is used in a reducible chain

The product recursion assumes positive neighboring rates; zero rates can split the state space into separate classes.

### Harmonic equations are asserted without boundary data

The interior equation alone does not determine the hitting probability. Include both endpoint values and prove uniqueness.

### Optional stopping is applied directly at an unbounded time

Stop first at τ∧T and justify the limit using absorption and boundedness.

## 10. Exercises

1. Define the finite birth–death generator and prove its rows sum to zero.
2. Derive the stationary weights from edge detailed balance.
3. Normalize the finite-capacity queue distribution for ρ=1 and ρ≠1.
4. Derive the first-difference recurrence for the two-boundary hitting probability.
5. Solve the symmetric gambler’s-ruin problem and verify the harmonic equation.
6. Prove uniqueness of a harmonic function with fixed endpoint values.
7. Verify that \(u_i=i(N-i)/(2c)\) solves the symmetric absorption-time equation.
8. Give a uniform finite-time lower bound on the probability of absorption from every interior state.
9. Express the Dirichlet form as a sum over path edges.
10. Identify the Lean boundary cases that arise from Fin (N+1) indexing.

## 11. The discrete maximum principle in detail

The uniqueness assertion used for hitting probabilities is worth isolating because the same argument appears in elliptic equations, potential theory, and finite-volume numerical schemes. Suppose (g_0=g_N=0) and (Qg(i)=0) at every interior state. If (g) has a positive maximum at an interior state i, then both differences (g_{i+1}-g_i) and (g_{i-1}-g_i) are nonpositive. Since the rates are nonnegative, (Qg(i)leq0). Equality forces every neighbor reached at positive rate to have the same value as g_i. Under strictly positive neighbor rates, this propagates the maximum along the path to a boundary, contradicting the zero boundary value unless the maximum is zero. Applying the same argument to −g rules out a negative minimum. Hence g vanishes identically.

For a formal proof, do not rely on an informal choice of a point where the maximum is attained. On a finite type, use a finite maximum or an argument by contradiction that chooses an index with maximal value. One convenient route is to prove a local lemma: if i is interior, (Qg(i)=0), and (g_i) is at least both neighboring values, then positive rates imply the neighbors equal (g_i). An induction propagates equality toward an endpoint. If the library maximum API is awkward for the chosen function type, an equivalent proof uses the first index at which a positive maximum is attained and examines the local equation there.

There is also an algebraic proof. Restrict the generator to interior states and move the boundary terms to the right-hand side. The resulting Dirichlet matrix is invertible: its kernel is trivial by the maximum principle, and a square linear map on a finite-dimensional space with trivial kernel is bijective. This gives existence and uniqueness for every boundary datum, not just the particular endpoint values 0 and 1. The analytic-looking maximum principle is therefore also a compact proof of a linear-algebra fact.

The hypotheses matter. If a rate vanishes in the interior, the path may split into communicating classes, and a harmonic function can be constant on each component with different constants. A clean theorem states positivity of both neighbor rates on the interior as an assumption, rather than trying to hide it in a coercivity argument.

## 12. A one-sided hitting-time formula

The two-boundary problem has a companion formula when the left endpoint reflects and the right endpoint is absorbing. Let the chain live on ({0,ldots,N}), with (mu_0=0), positive (lambda_i) for (i<N), and positive (mu_i) for (i>0). Let (T_N) be the first hitting time of N. Write (u_i=mathbb E_i[T_N]), so (u_N=0) and (Qu=-1) for (0leq i<N). Define the increments (Delta_i=u_i-u_{i+1}).

Let π be the stationary distribution of the chain when N is also reflecting, and let (c_i=pi_ilambda_i=pi_{i+1}mu_{i+1}). Multiplying the Poisson equation by (pi_i) gives, for (i<N),
\[
  c_i\Delta_i-c_{i-1}\Delta_{i-1}=\pi_i,
\]
where the term with (c_{-1}\Delta_{-1}) is understood as zero at i=0. Summing from 0 through k telescopes:
\[
  c_k\Delta_k=\sum_{j=0}^{k}\pi_j.
\]
Consequently,
\[
  u_0=\sum_{k=0}^{N-1}\Delta_k
     =\sum_{k=0}^{N-1}\frac{\sum_{j=0}^{k}\pi_j}{c_k}.
\]
More generally, (u_i=sum_{k=i}^{N-1}(sum_{j=0}^{k}\pi_j)/c_k). This representation separates a cumulative mass to the left of an edge from the edge’s conductance. A bottleneck with small (c_k) contributes a large expected crossing time, while the cumulative mass records how much stationary probability must be transported across it.

Although π was introduced as the stationary law for a reflecting chain, its weights are only used to express the reversible edge identities. The same calculation can use unnormalized weights (w_i): both numerator and denominator scale by the same constant, so the formula is unchanged. This is often the more convenient formal statement because it avoids proving the normalizing constant is nonzero until after the recurrence has been solved.

In Lean, prove the telescoping identity as a theorem about finite sums before substituting the probabilistic interpretation. A useful sequence of lemmas is: the edge-flux recurrence, the prefix-sum formula for (c_k\Delta_k), and a final sum for (u_i). The crucial induction step is cancellation of the previous prefix sum; it is a good use of `Finset.sum_range_succ` after arranging indices as natural numbers. Keep the chain’s boundary convention in the recurrence lemma explicit, since the i=0 case is exactly where the missing incoming edge disappears.

## 13. From the recurrence to a formal development

The mathematics in this chapter has three layers, and the Lean file layout should reflect them.

**Rate data.** Package the interval size and the two rate functions together with proofs of nonnegativity, boundary zeros, and (when needed) interior positivity. This object represents the model. The boundary facts should be fields or named hypotheses, so downstream theorems do not repeatedly unfold a `if i = 0 then ...` definition.

**Finite algebra.** Define the generator matrix and establish its action on observables. Prove stationary weights, the harmonic recurrence, the Poisson recurrence, and the conductance identities at this layer. The statements should quantify over real-valued rates and functions; no sample path is needed to prove that a proposed formula solves a finite equation. The maximum principle then supplies uniqueness.

**Probability.** Introduce the process and its stopping time only after the algebraic solution is available. Apply Dynkin’s formula at bounded stopping times, then prove absorption or integrability and pass to a limit. This architecture lets the algebraic chapter survive a change in the chosen process library or a later switch from continuous time to the embedded jump chain.

An informal dependency picture is:

```text
rate assumptions ──> generator identities ──> finite recurrence solutions
                                                │
                                                v
process + Dynkin formula ──> stopped expectations ──> hitting-time theorem
```

The diagram is deliberately a dependency graph rather than a proof script. The top line can be completed with finite sums and linear algebra. The bottom line consumes those results and handles measure-theoretic limits. When a Lean goal becomes difficult, locating it on this graph helps distinguish an indexing problem from a stopping-time problem.

## 14. Extension to nonuniform meshes and barriers

The state space need not represent queue length. It may represent the number of successes in a population, a discretized spatial coordinate, or a level in a reliability model. The birth and death rates can vary arbitrarily with i. The formulas above then describe how local drift and local bottlenecks combine over the whole interval.

One can also stop at two interior barriers a and b with (0\leq a<b\leq N). Restrict attention to ({a,a+1,\ldots,b}), set the boundary values at a and b, and repeat the difference argument. The harmonic solution becomes a ratio of sums of edge resistances between the barriers. In the reversible notation, the increment across edge k is proportional to (1/c_k); hence
\[
  h_i=\frac{\sum_{k=a}^{i-1}c_k^{-1}}{\sum_{k=a}^{b-1}c_k^{-1}}.
\]
This expression is the one-dimensional electrical-network formula: conductances in series combine through reciprocal resistance. It also follows directly from (c_k(h_{k+1}-h_k)) being constant, obtained by multiplying (Qh=0) by π and telescoping.

The barrier formulation illustrates a useful formalization principle: prove a theorem with arbitrary ordered endpoints, then instantiate it at 0 and N. If the theorem only works for the global endpoints, its proof may have accidentally depended on a convenient boundary simplification. General endpoints expose the real invariant and make the result reusable for hitting subintervals, comparison arguments, and domain decomposition.

## Summary

A finite birth–death chain has a generator supported on adjacent states. Its stationary law is obtained from local edge-balance recurrences; its hitting probabilities solve a harmonic recurrence; and expected absorption times solve a Poisson equation. Reversibility turns the Dirichlet form into a weighted sum over path edges. Formal proofs benefit from separating boundary handling, finite recurrences, and the process-level stopping argument.

## Further reading

- Chapters 55, 58, and 60 for generators, Dynkin’s formula, and Dirichlet forms.
- Chapter 37 for stopping times and optional sampling.
- Chapter 48 for total-variation convergence and contraction.

## 15. Lean formalization: a three-state hitting problem

On the interval `{0,1,2}`, let the birth rate be `a` on both edges and the
death rate be `b`. The proposed probability of hitting 2 before 0 is
`a / (a + b)` at state 1. The proposed expected absorption time is
`1 / (a + b)`. We verify the boundary values and the harmonic and Poisson
equations, then prove that each solution is unique among functions with the
specified boundary values. These are finite algebraic results; identifying
the solutions with process probabilities and expectations still requires
the stopping-time argument discussed in the chapter.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

theorem birthRateFromZero : twoStateGenerator zero one = 1 := by decide
theorem deathRateFromOne : twoStateGenerator one zero = 2 := by decide
theorem birthDeathRowBalance :
    generatorRowSum twoStateGenerator zero = 0 := generator_zero_row
```

The three-state generator records only transitions to adjacent states.

```lean
import Mathlib
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def threeStateBirthDeathGeneratorQ (a b : ℚ) (i j : Fin 3) : ℚ :=
  if i = 0 then (if j = 0 then -a else if j = 1 then a else 0)
  else if i = 1 then
    (if j = 0 then b else if j = 1 then -(a + b) else a)
  else if j = 1 then b else if j = 2 then -b else 0

def threeStateBirthDeathActionQ (a b : ℚ) (f : Fin 3 → ℚ)
    (i : Fin 3) : ℚ :=
  threeStateBirthDeathGeneratorQ a b i 0 * f 0 +
    threeStateBirthDeathGeneratorQ a b i 1 * f 1 +
    threeStateBirthDeathGeneratorQ a b i 2 * f 2

def threeStateHittingProbabilityQ (a b : ℚ) (i : Fin 3) : ℚ :=
  if i = 0 then 0 else if i = 1 then a / (a + b) else 1

def threeStateExpectedTimeQ (a b : ℚ) (i : Fin 3) : ℚ :=
  if i = 1 then 1 / (a + b) else 0

theorem three_state_hitting_probability_boundary_values (a b : ℚ) :
    threeStateHittingProbabilityQ a b 0 = 0 ∧
      threeStateHittingProbabilityQ a b 2 = 1 := by
  simp [threeStateHittingProbabilityQ]

theorem three_state_hitting_probability_harmonic (a b : ℚ)
    (h : a + b ≠ 0) :
    threeStateBirthDeathActionQ a b (threeStateHittingProbabilityQ a b) 1 = 0 := by
  simp [threeStateBirthDeathActionQ, threeStateBirthDeathGeneratorQ,
    threeStateHittingProbabilityQ]
  field_simp [h]
  ring

theorem three_state_harmonic_solution_unique (a b : ℚ)
    (h : a + b ≠ 0) (f : Fin 3 → ℚ)
    (h0 : f 0 = 0) (h2 : f 2 = 1)
    (hharmonic : threeStateBirthDeathActionQ a b f 1 = 0) :
    f 1 = a / (a + b) := by
  have hform : b * f 0 - (a + b) * f 1 + a * f 2 = 0 := by
    have hh := hharmonic
    simp [threeStateBirthDeathActionQ, threeStateBirthDeathGeneratorQ] at hh
    nlinarith [hh]
  rw [h0, h2] at hform
  field_simp [h] at hform ⊢
  nlinarith

theorem three_state_expected_time_boundary_values (a b : ℚ) :
    threeStateExpectedTimeQ a b 0 = 0 ∧
      threeStateExpectedTimeQ a b 2 = 0 := by
  simp [threeStateExpectedTimeQ]

theorem three_state_expected_time_poisson_equation (a b : ℚ)
    (h : a + b ≠ 0) :
    threeStateBirthDeathActionQ a b (threeStateExpectedTimeQ a b) 1 = -1 := by
  simp [threeStateBirthDeathActionQ, threeStateBirthDeathGeneratorQ,
    threeStateExpectedTimeQ]
  field_simp [h]
  ring

theorem three_state_poisson_solution_unique (a b : ℚ)
    (h : a + b ≠ 0) (f : Fin 3 → ℚ)
    (h0 : f 0 = 0) (h2 : f 2 = 0)
    (hpoisson : threeStateBirthDeathActionQ a b f 1 = -1) :
    f 1 = 1 / (a + b) := by
  have hform : b * f 0 - (a + b) * f 1 + a * f 2 = -1 := by
    have hp := hpoisson
    simp [threeStateBirthDeathActionQ, threeStateBirthDeathGeneratorQ] at hp
    nlinarith [hp]
  rw [h0, h2] at hform
  field_simp [h] at hform ⊢
  nlinarith
```
