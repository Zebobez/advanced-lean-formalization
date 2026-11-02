# Chapter 61 — Time-Inhomogeneous Chains and Evolution Families

> **Audience.** This chapter assumes familiarity with finite-state continuous-time Markov chains, matrix differential equations, and transition kernels. It extends generator methods to rates that change with time.

A time-homogeneous chain uses the same generator at every time. Many models instead have rates that depend on the calendar time: a system may fail more often as it ages, a queue may face rush-hour demand, or a biological process may respond to a changing environment. There is then no single matrix exponential \(e^{tQ}\) that describes every transition interval.

The correct replacement is an evolution family \(U(s,t)\), the transition matrix from time s to time t. It satisfies a two-time composition law and two differential equations, one for each time variable. When generators at different times fail to commute, chronological order matters. This chapter develops the finite-state theory and shows how a formalization can use products, integral equations, or a common Poisson clock.

## Learning objectives

By the end of the chapter, you should be able to:

- define a time-indexed family of finite-state generators;
- state the two-time composition law and forward/backward equations;
- compute transitions for piecewise-constant generators in the correct order;
- explain why integrating the generator and exponentiating is not generally valid;
- construct a nonhomogeneous chain by time-dependent uniformization;
- separate matrix evolution from the path-space process.

## 1. A generator that changes with time

Let S be finite. For every time t≥0, let Q_t be a generator matrix. Thus for x≠y,
\[
  q_t(x,y)\geq0,\qquad \sum_yq_t(x,y)=0.
\]
Assume the entries depend continuously on t. Because S is finite and a bounded time interval is compact, the exit rates are bounded on every interval [0,T]. A global bound may or may not exist on the full half-line.

Write U(s,t)(x,y) for the probability of state y at time t given state x at time s, where 0≤s≤t. For row distributions, evolution is
\[
  \mu_t=\mu_sU(s,t).
\]
The Chapman–Kolmogorov law becomes
\[
  U(s,t)=U(s,u)U(u,t),\qquad s\leq u\leq t,
\]
with U(t,t)=I. The family has two time arguments because the transition law can depend on where the interval begins, not only on its length.

For each s≤t, U(s,t) must be stochastic. The generator Q_t describes the infinitesimal transition at the terminal time when differentiating forward, and at the initial time when differentiating backward. That distinction produces the two Kolmogorov equations.

## 2. Forward and backward equations

Under the row-source convention, the forward equation differentiates the terminal time:
\[
  \frac{\partial}{\partial t}U(s,t)=U(s,t)Q_t,
  \qquad U(s,s)=I.
\]
It describes how the current distribution changes as the end of the interval moves forward.

The backward equation differentiates the initial time:
\[
  \frac{\partial}{\partial s}U(s,t)=-Q_sU(s,t),
  \qquad U(t,t)=I.
\]
The negative sign appears because increasing s shortens the interval at its left endpoint. These equations are consistent with the composition law, but they place the generator on opposite sides and evaluate it at different times.

In the homogeneous case Q_t=Q, the solution is U(s,t)=e^{(t-s)Q}; the two equations agree because Q commutes with its own exponential. In the nonhomogeneous case, it is not generally true that U(s,t) commutes with Q_s or Q_t. Proofs that silently move Q_t across U(s,t) have usually imported a homogeneous identity into the wrong setting.

The finite-dimensional assumption makes U a matrix-valued solution of a linear ODE. Standard existence and uniqueness theorems apply once the entries of Q_t have the required continuity. Stochasticity is an additional property: a general ODE solution need not be nonnegative or have row sums one. It follows here from the generator sign pattern, for example through approximating products of stochastic short-time transitions.

## 3. Chronological products

Suppose Q_t is constant on each interval of a partition
\[
  s=t_0<t_1<\cdots<t_n=t,
\]
with value Q_i on [t_i,t_{i+1}). Then
\[
  U(s,t)=
  e^{(t_1-t_0)Q_0}
  e^{(t_2-t_1)Q_1}\cdots
  e^{(t_n-t_{n-1})Q_{n-1}}.
\]
The earliest interval appears on the left because a row distribution multiplies transitions in chronological order:
\[
  \mu_s\longmapsto \mu_sU(t_0,t_1)
  \longmapsto \mu_sU(t_0,t_1)U(t_1,t_2).
\]
Each factor is stochastic, so their product is stochastic.

A rate switch is not itself a state transition. It changes the law governing
future holding times, but the path stays at its current state at the
switching instant unless a jump event also occurs there. For a finite
piecewise-constant schedule, define U by multiplying the interval
semigroups. The resulting matrix is continuous in its endpoints and
differentiable inside each phase; at a switch, use the one-sided equations
on the adjacent intervals rather than demanding a derivative that need not
exist.

This finite-product form is especially useful in a formal proof. It avoids solving a variable-coefficient ODE immediately and makes the transition order explicit. For a continuous Q_t, approximate time by partitions and prove convergence of the products to the evolution family. The analytic work is then a limit theorem for matrix products.

One positivity-preserving approximation uses Euler factors
\[
  E_i=I+\Delta_iQ_{t_i},\qquad \Delta_i=t_{i+1}-t_i.
\]
If \(\Delta_i\Lambda\leq1\) for a bound Λ on the exit rates, each E_i is
stochastic: its off-diagonal entries are nonnegative and its diagonal
entries are \(1-\Delta_i\lambda_{t_i}(x)\geq0\). Products of these factors
are stochastic. As the mesh tends to zero, the products converge to the
solution of the matrix integral equation. Entrywise limits preserve
nonnegativity and row sums, so stochasticity passes to U(s,t).

This proof route isolates an analytic approximation theorem from the
probability argument. A Lean development can first prove that every finite
Euler product is stochastic, then state convergence in a matrix norm, and
finally transfer the closed coordinate inequalities to the limit. The
rate bound is local to the interval being approximated; a different
partition and bound may be used on a later finite horizon.

## 4. Why the integrated generator is not enough

A tempting formula is
\[
  U(s,t)\stackrel{?}{=}
    \exp\!\left(\int_s^tQ_r\,dr\right).
\]
It is valid if the matrices Q_r commute pairwise for all r in the interval. Without commutativity, the product order carries information that the ordinary integral forgets.

Consider a two-state system with two phases. In the first phase only the transition 0→1 is allowed, at rate one:
\[
  Q_1=\begin{pmatrix}-1&1\\0&0\end{pmatrix}.
\]
In the second phase only 1→0 is allowed:
\[
  Q_2=\begin{pmatrix}0&0\\1&-1\end{pmatrix}.
\]
For durations u and v, the actual transition matrix is
\[
  U=e^{uQ_1}e^{vQ_2}.
\]
Reversing the phases gives \(e^{vQ_2}e^{uQ_1}\), which is generally different. The first phase can move initial mass from 0 to 1, where the second phase can move it back; reversing the schedule changes which initial states benefit from which rate.

The commutator \(Q_1Q_2-Q_2Q_1\) is nonzero. This is a finite exact witness that chronology matters, and it is a useful regression example for a formal development. A proof should not replace the ordered product by the exponential of uQ₁+vQ₂ unless it also proves the needed commutation relation.

## 5. Integral equations and ordered expansions

The forward equation is equivalent to the integral equation
\[
  U(s,t)=I+\int_s^tU(s,r)Q_r\,dr.
\]
This form is well suited to existence proofs by successive approximation. Substituting the right-hand side repeatedly produces an ordered series whose terms integrate over simplices
\[
  s\leq r_1\leq r_2\leq\cdots\leq r_k\leq t.
\]
Each term preserves chronological order. This is the finite-dimensional time-ordered, or Dyson, expansion.

The ordered expansion is not merely a more elaborate notation for an ordinary exponential series. In the homogeneous case, products of Q at different integration variables all equal powers of the same matrix, and the simplex volume contributes the factorial denominator. In the nonhomogeneous case, the factors Q_{r_i} vary and cannot be rearranged arbitrarily.

For Lean, a product approximation can be easier than formalizing the full ordered series, especially when the target theorem is stability under perturbation. The integral equation is preferable when the theorem already concerns derivatives or when a general ODE uniqueness result is available. Select the representation based on the final theorem, and prove a comparison lemma if both views are needed.

## 6. Time-dependent uniformization

On a bounded interval [0,T], choose Λ>0 that bounds every exit rate of every Q_t. Define
\[
  R_t=I+\frac{Q_t}{\Lambda}.
\]
Each R_t is stochastic. Run a rate-Λ Poisson clock and, at a candidate event time r, update the state according to R_r. This gives a path construction with finitely many candidate events on bounded intervals.

Conditional on candidate event times \(s<r_1<\cdots<r_n<t\), the transition matrix is the ordered product
\[
  R_{r_1}R_{r_2}\cdots R_{r_n}.
\]
Average over the Poisson event times to obtain U(s,t). Unlike the homogeneous formula, this is not just a scalar Poisson weight times Rⁿ, since the transition matrix depends on the event time.

This construction proves positivity and conservation of mass term by term: every conditional product is stochastic, and the event-time law is a probability distribution. It also gives a non-explosion bound on each bounded interval. The rate bound may depend on T; to define a process for all t≥0, use consistent constructions on nested finite horizons or assume a single global bound.

Conditioning on the number and locations of candidate events gives the
ordered-integral representation
\[
  U(s,t)=e^{-\Lambda(t-s)}
   \sum_{n=0}^{\infty}\Lambda^n
   \int_{s<r_1<\cdots<r_n<t}
     R_{r_1}\cdots R_{r_n}\,dr_1\cdots dr_n.
\]
For n=0, the integral term is I. Each matrix product is stochastic, and
the scalar coefficients are the probabilities of the Poisson event count
after integrating over its ordered event times. Thus the formula makes
stochasticity explicit while retaining the time order.

The composition law follows by splitting candidate events into those
before and after an intermediate time u. Independent increments of the
clock give independent counts on [s,u] and [u,t]; concatenating their
ordered matrix products gives the product U(s,u)U(u,t). This proves the
evolution-family law directly from the path construction and shows why the
family depends on both endpoints.

Time-dependent uniformization is a useful bridge between Chapters 56–57 and the evolution-family approach. It turns an analytic positivity question into a probabilistic mixture, while the ordered product retains the calendar-time dependence.

## 7. Worked example: a time-varying one-way transition

Let the state space be {0,1}, with 1 absorbing and transition rate a(t) from 0 to 1. The generator is
\[
  Q_t=\begin{pmatrix}-a(t)&a(t)\\0&0\end{pmatrix}.
\]
Starting from 0 at time s, the probability of remaining in 0 through time t is the solution of
\[
  p_0'(s,t)=-a(t)p_0(s,t),\qquad p_0(s,s)=1.
\]
Therefore
\[
  U(s,t)(0,0)=e^{-\int_s^t a(r)\,dr},
  \qquad
  U(s,t)(0,1)=1-e^{-\int_s^t a(r)\,dr}.
\]
The integrated hazard works here because a one-way survival probability is scalar. The matrix generator values at different times also commute in this example, so the ordinary exponential formula is valid.

This is a useful model of time-varying failure or arrival rates. It also illustrates a proof economy: solve a scalar ODE for survival and obtain the other transition probability by the row-sum identity. A full two-by-two matrix exponential calculation would be unnecessary.

If a(t)=a₁ on [s,c) and a(t)=a₂ on [c,t], then
\[
  U(s,t)(0,0)=e^{-a_1(c-s)-a_2(t-c)}.
\]
Multiplying the two phase matrices gives the same survival entry. The
generator values commute because each is a scalar multiple of one fixed
matrix, so this example is an instance where integrating the generator
does recover the ordered product. It gives a useful test: a general
time-inhomogeneous proof should reduce to this formula when all rates vary
through a common scalar factor.

## 8. Worked example: switching transition directions

Use Q₁ and Q₂ from Section 4, with the first phase lasting u and the second lasting v. The first matrix exponential is
\[
  e^{uQ_1}=
  \begin{pmatrix}e^{-u}&1-e^{-u}\\0&1\end{pmatrix},
\]
and the second is
\[
  e^{vQ_2}=
  \begin{pmatrix}1&0\\1-e^{-v}&e^{-v}\end{pmatrix}.
\]
The transition over both phases is their product in that order. Both factors are stochastic, so the result is stochastic even though the two generators do not commute.

Writing \(p=e^{-u}\) and \(q=e^{-v}\), the two possible orders are
\[
  e^{uQ_1}e^{vQ_2}
    =\begin{pmatrix}1-q+pq&q(1-p)\\1-q&q\end{pmatrix},
  \qquad
  e^{vQ_2}e^{uQ_1}
    =\begin{pmatrix}p&1-p\\p(1-q)&1-p+pq\end{pmatrix}.
\]
For u,v>0, the upper-left entries differ. The algebra makes the
noncommutation visible without a general commutator calculation and gives
an exact pair of normal forms for a Lean exercise.

This example can be formalized with matrix multiplication and scalar exponential identities. It tests three conventions at once: source states index rows, distributions multiply on the left, and earlier time intervals multiply before later intervals. A useful theorem states that the ordered product solves the piecewise-constant forward equation on each subinterval and is continuous at the switching time.

## 9. Formalization strategy

Expose an evolution-family interface with the following data:

1. U(s,t) is defined for s≤t and equals I when s=t.
2. U(s,t) is stochastic.
3. U(s,t)=U(s,u)U(u,t) for intermediate u.
4. U is continuous in both time variables and differentiable where the generator is continuous.
5. The forward and backward equations use the agreed row-source convention.

For a piecewise-constant generator, define U by a finite chronological product. For a continuous generator, choose either the integral equation or an ODE solution and prove the other characterization as a theorem. The time-dependent uniformization route is attractive when stochasticity and path construction matter more than differentiability.

Mathlib provides finite matrix exponentials, integration, and composition of Markov kernels. These tools support constant pieces, integral identities, and the measurable transition layer. The evolution-family construction for a chosen Q_t, including its positivity and chronological approximation, remains a theorem to build for the application.

If a later chapter needs only a fixed pair s,t, it may be enough to work with a stochastic matrix U(s,t). If it needs conditional laws over intermediate times, retain the composition equation. If it needs pathwise event times or adaptedness, construct the time-inhomogeneous process and filtration explicitly rather than treating the evolution family as a sample path.

## 10. Common failure modes

### The transition depends only on elapsed time

For a calendar-time-dependent generator, U(s,t) generally depends on both endpoints.

### The generator is put on the wrong side

Under row distributions, the forward equation is UQ_t; the backward equation is −Q_sU.

### The time-ordered product is reversed

Write the evolution of a row distribution one interval at a time to check factor order.

### A matrix integral is exponentiated without commutativity

Pairwise commutation is the hypothesis that permits the simple exponential formula.

### Local rate bounds are treated as global

A bound on each finite interval gives local non-explosion; it does not supply one uniform clock for the entire half-line.

## 11. Exercises

1. Derive the forward and backward equations from the composition law.
2. Prove the integral equation by integrating the forward equation.
3. Verify that the two switching generators in Section 4 do not commute.
4. Compute both phase orders and show that their products differ for suitable u,v>0.
5. Solve the one-way time-dependent chain using its integrated hazard.
6. Show that a piecewise-constant evolution is a product of stochastic matrix exponentials.
7. Prove time-dependent uniformization preserves row sums and entrywise nonnegativity.
8. State the extra hypothesis that makes exp(∫Q_r dr) a valid formula.
9. Explain why a rate bound depending on T is enough for each finite-horizon construction.
10. Design a Lean structure for U(s,t) that records the composition law without baking in a particular construction.

## Summary

A time-inhomogeneous finite-state chain is described by an evolution family U(s,t), not by a one-parameter semigroup. Its transitions compose across intermediate times and satisfy forward and backward equations with different generator order. Piecewise-constant rates produce chronological products; continuous rates can be handled by integral equations or time-dependent uniformization. Ordinary exponentiation of the integrated generator requires commutation.

## Further reading

- [Mathlib: Matrix exponential](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/MatrixExponential.html)
- [Mathlib: Markov kernel composition](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html)
- [Mathlib: Bochner integration](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html)
- Chapters 55–56 for homogeneous generators and uniformization.
- Chapter 59 for time-dependent potentials and the warning about noncommuting operators.
