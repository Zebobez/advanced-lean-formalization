# Chapter 59 — Feynman–Kac Semigroups and Killing

> **Audience.** This chapter assumes familiarity with finite-state generators, matrix exponentials, Markov processes, and time integrals. It studies expectations weighted by additive path functionals and their representation by a modified generator.

The transition semigroup records the distribution of the state at a future time. Many problems ask for more than the terminal state: they weight a path according to how long it spends in selected states, how much reward it accumulates, or whether a killing event has occurred. In a finite-state chain, these weighted expectations form another semigroup. Its generator is the original generator plus or minus a diagonal potential.

This is the finite-state Feynman–Kac principle. It connects path integrals to matrix exponentials and gives a practical route to survival probabilities, occupation-time transforms, and sensitivity calculations. The proof should keep three objects distinct: the original Markov semigroup, the path-dependent weight, and the modified linear operator that represents their combined expectation.

## Learning objectives

By the end of the chapter, you should be able to:

- define a weighted transition operator using an additive path functional;
- derive the modified generator for a finite-state chain;
- interpret nonnegative potentials as killing rates;
- distinguish a substochastic killed semigroup from a Markov semigroup;
- use Duhamel’s formula to compare weighted and unweighted dynamics;
- organize path integrals and matrix exponentials as separate Lean interfaces.

## 1. Additive path functionals

Let S be finite, let X be a continuous-time Markov chain with generator Q, and let V:S→ℝ be a potential. Along a path define the accumulated potential
\[
  A_t=\int_0^t V(X_s)\,ds.
\]
For an observable f:S→ℝ, define the weighted operator
\[
  (T_t^Vf)(x)
    =\mathbb E_x\!\left[e^{-A_t}f(X_t)\right].
\]
The subscript x means that the chain starts from x. When V is nonnegative, paths that spend more time in high-potential states receive smaller weight. If V is allowed to be negative, the weight rewards such paths instead.

Because S is finite, V and f are bounded. On each bounded time interval, the exponential weight is bounded above by \(e^{t\|V\|_\infty}\), so the expectation is finite. This bound justifies the basic integrability needed to define T_t^V.

The integral is a path functional, not a function of X_t alone. Two paths can have the same endpoint and different accumulated potentials. Replacing A_t by tV(X_t) would define a different model except in special cases such as constant V. This distinction matters in both mathematics and code: the path integral belongs to the process layer, while the resulting family of operators can be represented by finite matrices.

## 2. The weighted semigroup law

The additivity of the path integral gives
\[
  A_{s+t}=A_s+\int_s^{s+t}V(X_u)\,du.
\]
Condition on the information at time s. The Markov property says that the future path, given X_s, has the law of a fresh chain started at X_s. Therefore
\[
  T_{s+t}^V f=T_s^V(T_t^Vf),\qquad T_0^V=I.
\]
The weight splits into a factor for the first segment and a factor for the second segment. This is why an integral over the entire path can still produce a semigroup.

The argument depends on the additive form of A_t. A path penalty that does not split at intermediate times will not generally yield a semigroup on the original state space. It may require enlarging the state to include the relevant accumulated information, or using a two-parameter evolution family instead.

For V≥0, the operator preserves nonnegative functions and is dominated by the ordinary transition operator:
\[
  0\leq T_t^V f\leq P_t f\quad\text{when }f\geq0.
\]
In particular, \(T_t^V\mathbf 1\leq\mathbf 1\). The weighted operator is then a positive substochastic operator: it can lose mass because the path weight is at most one. For signed V, positivity of the operator remains, but the mass may increase, so it is not a sub-Markov transition kernel.

## 3. The modified generator

Let D_V be the diagonal matrix with entries D_V(x,x)=V(x). The weighted semigroup is represented by
\[
  T_t^V=e^{t(Q-D_V)}.
\]
Its generator acts on observables by
\[
  ((Q-D_V)f)(x)=(Qf)(x)-V(x)f(x).
\]
The extra term is local: while the chain occupies x, the path weight changes at instantaneous rate \(-V(x)\). The transition part remains Q.

One way to derive this generator is to examine a short time interval h. Starting at x, with probability \(1-\lambda(x)h+o(h)\) there is no state change, and the weight contributes \(1-V(x)h+o(h)\). A jump from x to y contributes \(q_{xy}h+o(h)\). Combining the first-order terms gives
\[
  T_h^Vf(x)=f(x)+h\bigl((Qf)(x)-V(x)f(x)\bigr)+o(h).
\]
The semigroup property then identifies T_t^V as the solution of the finite-dimensional linear differential equation with initial value I and generator Q−D_V.

An equivalent derivation uses the path construction from Chapter 57 and the Feynman–Kac formula for finite-state continuous-time chains. In Lean, the short-time derivation may involve path and jump estimates; proving a semigroup identity and its derivative can be cleaner when the needed analytic lemmas are already available. Either way, stochasticity should not be claimed for T_t^V unless V is zero. With a nonnegative potential, the correct property is substochasticity.

To make the identification rigorous, first prove that the weighted family
is a semigroup, then establish its derivative at zero from the one-step
expansion. The semigroup law transports this derivative to every time:
the right derivative at t is (Q−D_V)T_t^V.
Finite-dimensional uniqueness for the linear differential equation then
identifies the family with the matrix exponential. Keeping uniqueness as a
named theorem prevents the path calculation from being repeated for every
entry of the transition operator.

## 4. Duhamel’s formula

The original semigroup P_t=e^{tQ} and the weighted semigroup T_t^V=e^{t(Q-D_V)} differ by the diagonal perturbation. Variation of constants gives
\[
  T_t^V-P_t
   =-\int_0^t P_sD_VT_{t-s}^V\,ds.
\]
Applied to f, this becomes
\[
  T_t^Vf-P_tf
   =-\int_0^t P_s\bigl(V\cdot T_{t-s}^Vf\bigr)\,ds.
\]
The order of the factors matters when Q and D_V do not commute. The formula describes the weighted evolution as ordinary evolution interrupted by the potential term.

For a constant potential V(x)=c, D_V=cI commutes with Q, so
\[
  T_t^V=e^{-ct}P_t.
\]
For a nonconstant V, it is generally incorrect to write \(e^{-tD_V}P_t\). The diagonal potential matrix need not commute with Q. Duhamel’s formula remains valid without that commutativity assumption.

The formula is also useful for perturbation bounds. If V is small in sup norm, the difference between T_t^Vf and P_tf can be bounded by integrating the magnitude of the potential term. Since finite-state Markov operators are contractions in the sup norm and the weighted operator is bounded on a finite horizon, one obtains estimates proportional to t‖V‖∞ times a suitable bound on f. The exact constant depends on whether V is signed and on the chosen operator norm.

## 5. Killing as an augmented Markov chain

Suppose V(x)≥0. Interpret V(x) as an additional rate at which the chain is killed while it occupies x. Add a cemetery state †. From x∈S, retain the original rates q_xy to other states and add a rate V(x) from x to †. The cemetery state is absorbing.

The generator of the augmented chain has row sum zero. Its restriction to S×S is Q−D_V, because the diagonal at x must include the additional outgoing killing rate. Therefore
\[
  (T_t^V\mathbf 1)(x)
    =\Pr_x(\text{the chain has not been killed by time }t).
\]
More generally, \(T_t^Vf(x)\) is the expected terminal value f(X_t) on the event of survival, with value zero after killing.

This interpretation explains the lost row mass. If one tries to turn the S×S matrix T_t^V into a Markov kernel without adding the cemetery state, the rows generally sum to less than one. Adding † restores total mass and turns the killed semigroup into an ordinary transition semigroup on the enlarged finite state space.

If V vanishes at a state, no killing transition leaves that state. If V is identically zero, the cemetery state is unreachable and T_t^V=P_t. These edge cases make useful normalization lemmas in a formal development.

## 6. Worked example: constant killing

Let V(x)=c for every state, with c≥0. Then
\[
  A_t=ct,\qquad
  T_t^Vf=e^{-ct}P_tf.
\]
The probability of survival to time t in the augmented-chain interpretation is e^{-ct}, independently of the state path. The original chain evolves normally conditional on survival.

This example gives a quick check on signs. The modified generator is Q−cI, whose diagonal entries are more negative than those of Q. A negative sign before c produces decay; changing it to Q+cI would instead weight paths by e^{ct}. For a matrix proof, use the fact that Q commutes with cI and factor the exponential. No pathwise integral estimate is required once the constant-potential identity has been established.

## 7. Worked example: killing in one state

Take a two-state chain with rates a from 0 to 1 and b from 1 to 0. Let killing occur only in state 1 at rate v≥0. Then
\[
  Q-D_V=
  \begin{pmatrix}
    -a&a\\
    b&-b-v
  \end{pmatrix}.
\]
The quantity \((T_t^V\mathbf 1)(0)\) is the probability that the chain, started at 0, has not been killed by time t. The row sums of the modified generator are 0 at state 0 and −v at state 1; after adjoining the cemetery transition of rate v, both rows of the full generator sum to zero.

This example can be formalized without diagonalizing the matrix. Prove the generator identity for the augmented three-state chain, restrict its transition matrix to the two live states, and identify that block with the exponential of Q−D_V. The block argument connects an actual killing construction with a matrix semigroup. Alternatively, if only survival probabilities are needed, work directly with the two-by-two weighted matrix and prove its row sums are at most one.

For f equal to the constant function one, write s₀(t) and s₁(t) for the
survival probabilities from the two initial states. The backward equation
for the weighted semigroup gives
\[
  s_0'=-a s_0+a s_1,\qquad
  s_1'=b s_0-(b+v)s_1,\qquad s_0(0)=s_1(0)=1.
\]
The first equation has no direct killing term because killing occurs only
in state 1. The second has the additional loss rate v. This small system
provides a direct check of the diagonal perturbation and is often simpler
to formalize than a closed-form expression involving the two eigenvalues.

## 8. Other uses of the potential

A signed weight \(e^{\int_0^t W(X_s)\,ds}\) corresponds to the operator Q+D_W rather than Q−D_V. This form generates exponential moments of occupation times and additive rewards. For example, if W is an indicator of a subset A, then
\[
  \mathbb E_x\!\left[e^{\theta\int_0^t\mathbf 1_A(X_s)\,ds}f(X_t)\right]
   =\bigl(e^{t(Q+\theta D_{\mathbf 1_A})}f\bigr)(x).
\]
Differentiating in θ at zero gives moments involving the time spent in A. The first derivative yields the expected occupation time; higher derivatives encode higher moments and correlations.

This method is also a finite-state version of a generating-function technique. Rather than tracking the full distribution of an additive statistic, place its exponential weight inside a semigroup and differentiate with respect to the parameter. In formalization, the matrix dependence on θ and the pathwise differentiation under expectation are distinct proof obligations. Boundedness of the state space and finite time interval gives useful domination for the latter.

For time-dependent potentials V_t, the operator at time t is Q−D_{V_t}. Unless these matrices commute at different times, the solution is not a single exponential of the integral of the generators. One obtains a two-parameter evolution family or a time-ordered exponential. A formal proof should not move the time integral inside a matrix exponential without a commutativity theorem.

### Occupation-time transforms

For a subset A of states, take W to be its indicator and define
\[
  B_t=\int_0^t\mathbf 1_A(X_s)\,ds.
\]
The operator
\[
  u_\theta(t,x)=\mathbb E_x[e^{\theta B_t}]
\]
is obtained by applying the matrix exponential of Q+θD_W to the constant
function. Differentiating at θ=0 recovers the expected occupation time:
\[
  \left.\frac{\partial}{\partial\theta}u_\theta(t,x)\right|_{\theta=0}
   =\int_0^t(P_s\mathbf 1_A)(x)\,ds.
\]
The derivative of a matrix exponential with respect to its matrix argument
has an integral formula. When applied to the constant function, the
rightmost transition operator fixes that function, leaving the displayed
occupation integral.

Higher derivatives encode moments of B_t. For example, the second
derivative contains two time integrations and records correlations between
visits to A at different times. This method avoids enumerating path
histories, whose number grows with the possible jump count. A Lean proof can
first establish the finite-matrix derivative formula, then identify the
resulting integral with the probabilistic moment using bounded convergence.

## 9. Formalization strategy

Separate the proof into four layers:

1. Define the diagonal operator D_V and prove its action on functions.
2. Establish measurability and integrability of the path functional A_t.
3. Prove the weighted semigroup property from additivity and the Markov property.
4. Identify its derivative at zero and solve the finite-dimensional evolution equation.

If the path construction from Chapter 57 is already available, finite-state boundedness gives \(|A_t|\leq t\|V\|_\infty\). This bound controls the exponential weight and supports integrability. If the development begins from transition kernels rather than sample paths, a path-space or Feynman–Kac construction is still needed to define the additive functional; the matrix exponential alone is not its probabilistic interpretation.

Mathlib supplies general matrix-exponential and integration interfaces that support the finite-dimensional algebra and calculus. A complete finite-state Feynman–Kac theorem still needs the bridge from the path integral to the modified generator. The cemetery-state construction offers a second route for nonnegative V: prove the augmented chain is Markov, then use its ordinary transition semigroup.

Keep the row-sum property visible. Q has zero row sums, Q−D_V has row sums −V(x), and the augmented generator restores the missing mass through the cemetery column. This three-way comparison is a powerful invariant for debugging signs and diagonal entries.

## 10. Common failure modes

### The endpoint is mistaken for the path functional

The accumulated potential depends on all states visited between zero and t, not only on X_t.

### A killed semigroup is called stochastic

For nonzero nonnegative V, mass is lost from the live state space. Use a sub-Markov property or add the cemetery state.

### The potential is added with the wrong sign

The weight exp(−A_t) gives Q−D_V. The reward weight exp(+A_t) gives Q+D_V.

### A nonconstant diagonal perturbation is factored from the exponential

The factorization requires commutation. D_V and Q usually do not commute.

### A time-dependent generator is integrated as if it commuted

The evolution requires time ordering unless the operators commute at different times.

## 11. Exercises

1. Prove the weighted semigroup law by conditioning at time s.
2. Derive the short-time expansion for T_h^V f.
3. Show that V≥0 implies T_t^V is positive and substochastic.
4. Construct the augmented generator with a cemetery state and verify its row sums.
5. Derive Duhamel’s formula for T_t^V−P_t.
6. Prove the constant-potential identity T_t^V=e^{-ct}P_t.
7. For the two-state example, compute the modified generator and identify the killing transitions.
8. Differentiate the occupation-time transform at θ=0 to obtain an expectation formula.
9. Explain why a time-varying potential generally requires a two-parameter evolution family.
10. State which lemmas depend on the path construction and which depend only on matrix calculus.

## Summary

Weighting paths by the exponential of an integrated potential produces a new semigroup with generator Q−D_V. For nonnegative V, this is a killed, substochastic evolution; adding a cemetery state restores a Markov chain. Duhamel’s formula compares the weighted and ordinary semigroups, while constant potentials factor cleanly because they commute with Q. Formal proofs should separate path-integral construction, operator calculus, and the interpretation of lost mass.

## Further reading

- [Mathlib: Matrix exponential](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/MatrixExponential.html)
- [Mathlib: Bochner integration and measure theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html)
- Chapters 32–33 for integration and product-measure arguments.
- Chapters 55–58 for generators, sample paths, and martingale formulas.

## 12. Lean formalization: the cemetery-state generator

The first block preserves the original constant-potential finite example.
The following blocks formalize the two-state killing calculation with
symbolic rates. On the live state space, the modified generator loses row
mass at rate `v` in state one. Adding the cemetery transition of rate `v`
restores zero row sums, and the live block agrees entry by entry with the
modified generator. These algebraic facts verify the killing construction;
they do not yet identify the corresponding matrix exponential with the
path-weighted expectation.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def killingPotential : State → Nat := fun _ => 1
def killedFlipWeight (i j : State) : Nat := killingPotential i * flipKernel i j

theorem constantKillingLeavesTheOffDiagonalWeight : killedFlipWeight zero one = 2 := by decide
```

The live-state generator `Q-D_V` has row sum zero at state zero and `-v` at
state one.

```lean
def killedTwoStateGenerator (a b v : ℚ) (i j : State) : ℚ :=
  if i = zero then (if j = zero then -a else a)
  else if j = zero then b else -(b + v)

def killedTwoStateRowSum (a b v : ℚ) (i : State) : ℚ :=
  killedTwoStateGenerator a b v i zero + killedTwoStateGenerator a b v i one

theorem killed_two_state_row_sums (a b v : ℚ) :
    killedTwoStateRowSum a b v zero = 0 ∧
      killedTwoStateRowSum a b v one = -v := by
  constructor
  · simp [killedTwoStateRowSum, killedTwoStateGenerator, zero, one]
  · simp [killedTwoStateRowSum, killedTwoStateGenerator, zero, one]
```

Use the third state as the cemetery state. From state one the augmented chain
keeps the original rate `b` to zero, changes its diagonal to `-(b+v)`, and
sends mass to the cemetery at rate `v`.

```lean
def augmentedKillingGenerator (a b v : ℚ) (i j : Fin 3) : ℚ :=
  if i = 0 then (if j = 0 then -a else if j = 1 then a else 0)
  else if i = 1 then (if j = 0 then b else if j = 1 then -(b + v) else v)
  else 0

def augmentedKillingRowSum (a b v : ℚ) (i : Fin 3) : ℚ :=
  augmentedKillingGenerator a b v i 0 +
    augmentedKillingGenerator a b v i 1 +
    augmentedKillingGenerator a b v i 2

theorem augmented_killing_generator_row_sums (a b v : ℚ) (i : Fin 3) :
    augmentedKillingRowSum a b v i = 0 := by
  fin_cases i
  · simp [augmentedKillingRowSum, augmentedKillingGenerator]
  · simp [augmentedKillingRowSum, augmentedKillingGenerator]
  · simp [augmentedKillingRowSum, augmentedKillingGenerator]

theorem augmented_killing_live_block (a b v : ℚ) :
    augmentedKillingGenerator a b v 0 0 = -a ∧
      augmentedKillingGenerator a b v 0 1 = a ∧
      augmentedKillingGenerator a b v 1 0 = b ∧
      augmentedKillingGenerator a b v 1 1 = -(b + v) := by
  norm_num [augmentedKillingGenerator]

theorem augmented_killing_rate_to_cemetery (a b v : ℚ) :
    augmentedKillingGenerator a b v 1 2 = v := by
  norm_num [augmentedKillingGenerator]
```
