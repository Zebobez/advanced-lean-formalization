# Chapter 57 — Sample Paths and Non-Explosion

> **Audience.** This chapter assumes familiarity with finite-state generators, uniformization, filtrations, and probability measures. It constructs path-valued versions of finite-state continuous-time chains and explains how to formalize their regularity.

Chapters 55 and 56 built a transition semigroup and gave a Poisson-clock representation. A stochastic process asks for more: on one probability space, it assigns a state to every time, and those states must have suitable measurability and path properties. This chapter turns the event-by-event description into a piecewise-constant path and proves the key finite-state safety property: only finitely many genuine jumps occur on every bounded time interval, almost surely.

The construction has two complementary forms. The jump-chain form records only actual state changes and gives each state its own exponential holding time. The uniformized form uses a single clock rate and permits self-transitions. The latter makes non-explosion and semigroup calculations especially transparent; the former gives the familiar interpretation in terms of successive holding times and destinations.

## Learning objectives

By the end of the chapter, you should be able to:

- separate the embedded jump chain from its holding times;
- construct a piecewise-constant process from a marked Poisson clock;
- prove non-explosion from a finite uniform rate bound;
- identify the path regularity obtained from the construction;
- distinguish finite-dimensional distributions from a path-space process;
- design Lean interfaces for sample paths, filtrations, and stopping times.

## 1. The embedded jump chain

Let S be finite and let Q be a generator. The exit rate from x is
\[
  \lambda(x)=\sum_{y\ne x}q_{xy}.
\]
When \(\lambda(x)>0\), define the destination law after a genuine jump by
\[
  J(x,y)=
  \begin{cases}
    q_{xy}/\lambda(x),&y\ne x,\\
    0,&y=x.
  \end{cases}
\]
Its row sum is one. When \(\lambda(x)=0\), the state is absorbing; it is useful to define J(x,x)=1 in that row, while separately recording that no future holding time ends.

Starting at \(X_0=x\), the holding time in state x has the exponential law with rate \(\lambda(x)\). At the end of that time, choose the next state using J(x,·), then repeat. Conditional on the sequence of visited states, the holding times are independent exponentials with the corresponding state-dependent rates. A zero exit rate is interpreted as an infinite holding time.

This representation separates two sources of randomness: how long the process remains in its current state, and which state it enters next. That separation is useful in proofs of hitting probabilities and path decompositions. It is also the origin of the common mistake of using q(x,y) directly as a destination probability. The rate must first be normalized by the total exit rate.

For a finite state space, every exit rate is bounded. Choose Λ>0 with λ(x)≤Λ for all x, and define the stochastic matrix R=I+Q/Λ from Chapter 56. The uniformized representation instead samples a rate-Λ Poisson clock and applies R at every ring. A ring may leave the state unchanged. Removing these self-transitions gives the jump-chain description. Keeping them gives a uniform clock that dominates every state-specific jump rate.

## 2. Building paths from event times

Let T₁<T₂<⋯ be the event times of a rate-Λ Poisson process, with T₀=0. Let Y₀,Y₁,… be a discrete-time Markov chain with transition matrix R, independent of the clock. Define
\[
  N_t=\#\{n\geq1:T_n\leq t\},\qquad
  X_t=Y_{N_t},\qquad t\geq0.
\]
At a clock event, the state is updated once; when R chooses the current state, the path remains constant. With the convention Tₙ≤t, the value at an event time is the post-update state, so paths are right-continuous.

The construction can be read as a sequence of marked event times:

**Clock:** 0 → T₁ → T₂ → T₃ → time  
**State:** Y₀ → Y₁ → Y₂ → Y₃  
**Rule:** each event applies R.

Some marks can repeat the current state. Those events are present in N_t, but they are not genuine jumps of X. The number of genuine jumps by time t is bounded by N_t.

For any fixed time t, the distribution of N_t is Poisson with mean Λt. Conditional on N_t=n, the state distribution is obtained by applying Rⁿ to the initial distribution. Averaging over n recovers the mixture
\[
  P_t=e^{-\Lambda t}\sum_{n=0}^{\infty}
        \frac{(\Lambda t)^n}{n!}R^n.
\]
The path construction therefore has exactly the transition matrices established in Chapter 56.

The Markov property follows from two independent-increment facts. Future Poisson events after time s are independent of the clock history up to s; future discrete transitions depend on the past only through the current state Y_{N_s}. Together, they imply that conditional on the information through time s, the law at time s+t is obtained by applying P_t to the state at time s.

## 3. Non-explosion by clock domination

An explosion would mean infinitely many genuine jumps in some bounded interval. The uniformized construction rules this out immediately. For every T≥0,
\[
  \#\{\text{genuine jumps in }[0,T]\}\leq N_T.
\]
The Poisson random variable N_T is finite almost surely. Therefore the number of genuine jumps on each fixed bounded interval is finite almost surely.

To obtain the path statement simultaneously for every bounded interval, it is enough to establish finiteness for each integer time horizon. The event that N_n is finite for all natural n is a countable intersection of probability-one events. Every finite real T lies below some integer n, and monotonicity gives N_T≤N_n. Thus almost every constructed path has only finitely many candidate events on every bounded interval.

This argument is stronger than a claim that each holding time is positive almost surely. A sequence of positive times can still have a finite sum. Non-explosion concerns the sum of infinitely many waiting times, or equivalently the count of jumps before a finite horizon. Domination by a Poisson clock controls the count directly.

The rate bound is essential to this proof. For a countably infinite state space, rates can grow without bound along the path, and no finite global Λ may exist. Then non-explosion requires a different Lyapunov or comparison argument. The finite-state theorem is a valuable base case, but its proof should not be presented as applying automatically to unbounded-rate chains.

## 4. Path regularity

Between consecutive candidate times, X_t is constant. At each event time, it takes its new value and remains there until the next event. Since there are finitely many candidate events on bounded intervals, the path is piecewise constant and has left limits everywhere at positive times. With the post-update convention, it is right-continuous. In probability theory this is called a càdlàg path.

Because S is finite with the discrete topology, every state-valued path obtained this way is Borel measurable as a function of time. For a fixed t, the event {X_t=x} can be written as the countable union over n of
\[
  \{N_t=n\}\cap\{Y_n=x\}.
\]
This gives a direct route to measurability of each random variable X_t. Joint measurability in time and sample point is a stronger statement; it can be proved from the event-time construction or obtained from a suitable measurable-process theorem. Keep the statement actually needed by the application explicit.

Right-continuity of paths should not be inferred from continuity of the transition probabilities in t. A family of one-time laws does not by itself specify how random variables at different times are coupled on one sample space. The marked-clock construction supplies this coupling and gives path regularity through its event times.

## 5. The natural filtration and stopping times

The natural filtration of X records all observations up to the current time:
\[
  \mathcal F_t^X=\sigma(X_s:0\leq s\leq t).
\]
The process is adapted to this filtration by construction. A filtration may be completed or made right-continuous for particular theorems, but those operations change the measurable spaces and should be introduced only when needed.

Define the first genuine jump time by
\[
  \tau_1=\inf\{t>0:X_t\ne X_0\}.
\]
It is a stopping time for the natural filtration: the event {τ₁≤t} is determined by the path observed through time t. Later jump times can be defined recursively, with the same stopping-time argument. If one instead uses candidate clock times, those are stopping times for the clock filtration; the state process may not jump at every candidate time.

The distinction between candidate and genuine jump times matters in optional-sampling arguments. A bound on the number of Poisson clock events controls the number of true jumps, but an identity for the process at a genuine jump time may require removing self-transitions. In a formalization, define both sequences rather than overloading one name.

## 6. Worked example: a two-state alternating chain

Take states 0 and 1, with rates a>0 from 0 to 1 and b>0 from 1 to 0. The jump chain alternates deterministically:
\[
  0,1,0,1,\ldots
\]
The holding times are independent exponentials, with rate a on visits to 0 and rate b on visits to 1. If a=b, the successive holding times are identically distributed; if the rates differ, the path still alternates but the durations in the two states have different laws.

Using uniformization at rate Λ≥max(a,b), the candidate clock rings at the same rate in either state. At state 0, each ring changes the state with probability a/Λ; at state 1, it changes the state with probability b/Λ. Otherwise the chain stays in place. This view is convenient for simulation; the alternating jump chain is more convenient for describing actual jump destinations.

The transition probability from 0 to 1 by time t is
\[
  P_t(0,1)=\frac{a}{a+b}\bigl(1-e^{-(a+b)t}\bigr).
\]
The pathwise holding-time construction and the matrix-semigroup calculation give the same expression. Comparing them is a useful consistency check: the path construction contributes meaning to the law, while the semigroup formula makes computation easier.

## 7. Worked example: a finite pure-death chain

Let the states be 0,1,2, with rate c>0 from 2 to 1 and rate d>0 from 1 to 0; state 0 is absorbing. A path started at 2 can visit only
\[
  2\longrightarrow1\longrightarrow0.
\]
The holding time at 2 is exponential with rate c, and after it the chain enters 1. The holding time at 1 is exponential with rate d, after which the chain remains at 0 forever. There are at most two genuine jumps, so non-explosion is deterministic in this example.

For a uniformized construction, choose Λ≥max(c,d). At state 2, a candidate event moves to 1 with probability c/Λ; at state 1, it moves to 0 with probability d/Λ; state 0 remains fixed. The Poisson construction may have infinitely many candidate events over an infinite time horizon, but only finitely many occur on every finite horizon, and only two can change the state.

This example demonstrates an important distinction: non-explosion does not mean that the process eventually stops receiving candidate clock events. It means that genuine state changes cannot accumulate at a finite time. An absorbing state can receive arbitrarily many self-transitions in the uniformized representation without any explosion of the state path.

## 8. Formalization architecture

A process-level development can be organized into declarations for:

1. the event-time sequence and its monotonicity;
2. the discrete chain of marks with transition matrix R;
3. the counting process and the piecewise-constant evaluation map;
4. measurability of X_t and almost-sure local finiteness of events;
5. path regularity and adaptation to a chosen filtration;
6. transition probabilities and the Markov property.

Avoid defining the whole path first as an opaque function and then proving every property from its formula. Expose lemmas that characterize the path at t by the number of events up to t; this is the bridge between probability on the event sequence and finite-state transition matrices.

### Realizing the clock and marks

One concrete sample space uses a sequence of independent exponential
interarrival times, each with rate Λ, together with the randomness used to
choose the next state from the appropriate row of R. The event times are
partial sums of the interarrival sequence. Their strict increase holds
almost surely because each exponential variable is positive almost surely.
The divergence of the partial sums gives local finiteness of the clock.

For a finite state set, a row of R is a finite probability mass function.
The next state can be sampled from that law using a uniform random variable,
or represented by a probability kernel from the current state. The kernel
view is usually more reusable: it states the conditional distribution
without committing to a particular random-number implementation. In either
case, the sequence of marks and the sequence of clock gaps must have the
independence needed by the construction.

This product-space description exposes the measurability proof. Each partial
sum is a measurable function of finitely many coordinates. The event that
exactly n clock rings have occurred by t is described by inequalities
between consecutive partial sums and t. The state event X_t=x is then a
countable union over n of intersections with the measurable mark event
Y_n=x. These reductions make the coordinate map X_t measurable without
requiring a general theorem about arbitrary path spaces.

There is a tradeoff. A probability-kernel construction emphasizes
conditional laws and composes well with Mathlib's kernel interfaces. A
uniform-variable construction emphasizes executable simulation. If the
book's theorem is distributional, prefer the kernel statement; if it studies
an algorithm, expose the sampler and prove that its law is the desired
kernel.

Mathlib provides general interfaces for filtrations, natural filtrations, adapted processes, stopping times, and probability measures. Those interfaces help state the result, but they do not automatically produce a CTMC sample space from a generator. The event-time distribution, independence of marks, and path regularity remain mathematical construction work. For many finite-state theorems, stop at the semigroup level and introduce paths only when the conclusion actually mentions sample paths or stopping times.

## 9. Common failure modes

### A finite-dimensional law is mistaken for a path construction

Consistent distributions at finitely many times do not by themselves prove right-continuous paths or identify jump times.

### Candidate events are called genuine jumps

Uniformization permits self-transitions. Keep the event count and the state-change count distinct.

### Positive holding times are assumed to prevent explosion

Infinitely many positive waiting times can have a finite sum. Use a count bound or a divergent-sum theorem.

### The embedded jump law is not normalized

Rates become destination probabilities only after dividing by the exit rate, and only when that rate is positive.

### Absorbing states are given an exponential clock of rate zero

Represent the holding time as infinite, or define absorption directly. The exponential distribution interface uses a positive rate.

## 10. Exercises

1. Define the embedded jump kernel for a finite generator and prove its rows sum to one, including absorbing states.
2. Express a fixed-time event {X_t=x} as a countable union over the number of candidate clock events.
3. Prove that the number of genuine jumps before T is bounded by the Poisson count N_T.
4. Extend the fixed-horizon non-explosion statement to all finite horizons using integer bounds.
5. Show that the piecewise-constant path is right-continuous under the post-update convention.
6. Prove that each coordinate random variable X_t is measurable when the state space is finite and discrete.
7. Identify the natural filtration and prove the first genuine jump time is a stopping time.
8. Compare the holding-time and uniformized constructions for the two-state chain.
9. Explain why a countably infinite state space may not admit one finite uniform rate bound.
10. For the pure-death example, state the maximum number of genuine jumps and explain why candidate events can be more numerous.

## Summary

The embedded jump chain separates destination choices from state-dependent exponential holding times. Uniformization gives a second construction on one probability space: a rate-Λ Poisson clock supplies candidate events, and a stochastic matrix supplies a state mark at each event. Since genuine jumps are bounded by the Poisson event count, finite-state chains with bounded rates do not explode. The construction also yields piecewise-constant càdlàg paths, coordinate measurability, and a natural filtration, while keeping candidate events distinct from actual jumps.

## Further reading

- [Mathlib: Exponential distributions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Exponential.html)
- [Mathlib: Filtrations and natural filtrations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Filtration.html)
- [Mathlib: Adapted and progressively measurable processes](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Adapted.html)
- Chapter 56 for the Poisson-mixture formula and the stochastic uniformized matrix.
- Chapters 36–37 for filtrations, stopping times, and optional sampling.
