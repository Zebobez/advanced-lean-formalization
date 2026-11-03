# Chapter 66 — Graphical Constructions for Finite Particle Systems

> **Audience.** This chapter assumes the finite-state generator and local-update machinery of Chapters 55 and 64, together with the coupling ideas from Chapter 62. The emphasis is on representing a stochastic path by a finite family of event clocks and deterministic update maps.

An interacting particle system may have exponentially many configurations, even though a single event changes only one site or one edge. A graphical construction records the events as marks in space-time and applies a deterministic update at each mark. This viewpoint has two advantages. It makes pathwise coupling almost automatic, and it exposes the generator as a sum of local event operators. On a finite graph, the construction is elementary: there are finitely many event types and their total rate is bounded.

This chapter formalizes that finite setting. It develops a general random-map construction, studies the voter and contact processes as examples, and explains what changes when one later passes to infinite graphs.

## Learning objectives

By the end of this chapter, you should be able to:

- encode event types as rates and deterministic maps on a finite state space;
- recover the continuous-time generator from a marked Poisson construction;
- couple processes by sharing the same event marks;
- prove monotonicity by checking each event map preserves an order;
- state voter-model duality through backward tracing of graphical arrows;
- separate finite-path proofs from limits needed for infinite systems.

## 1. Events as random maps

Let Ω be a finite configuration space and let E be a finite type of events. Each event e has a rate (r_e\geq0) and an update map (T_e:\Omega\to\Omega). When event e occurs, the new state is (T_e(x)). Several event types may produce the same transition; their rates simply add. Some events may leave the state unchanged, in which case they are null events for the state process.

For an observable f, the generator is
\[
  (Lf)(x)=\sum_{e\in E}r_e\bigl(f(T_e(x))-f(x)\bigr).
\]
The constant function is annihilated term by term, so the rows sum to zero. The transition rate from x to y with (y\ne x) is
\[
  q(x,y)=\sum_{e:\,T_e(x)=y}r_e.
\]
The total exit rate is at most (R=\sum_e r_e). A state-dependent implementation may include events whose map is currently a no-op; these events increase the clock rate but do not change the generator.

Assign to each event e an independent Poisson clock of rate r_e. At every clock ring, apply T_e. Because E is finite, the superposition has rate R, and only finitely many marks occur in a bounded time interval almost surely. This defines a path by composing the event maps in chronological order.

There is an equivalent uniformized construction. Run a single Poisson clock of rate R. At each tick choose event e with probability (r_e/R); if R exceeds the sum of active event rates, assign the remaining probability to a do-nothing event. The resulting generator is still L. This equivalence connects graphical constructions with Chapter 56’s uniformization.

## 2. Pathwise composition and the generator

Suppose the event marks in ([0,t]) are ((e_1,s_1),\ldots,(e_m,s_m)), ordered by time. Then the state is
\[
  X_t=T_{e_m}\circ\cdots\circ T_{e_1}(X_0).
\]
Poisson processes have no simultaneous marks almost surely when there are finitely many independent clocks with continuous waiting-time laws. If one wants to define the path on every sample point, fix a deterministic tie-breaking order on E; this affects only a null event but removes ambiguity from a total definition.

For a small time interval of length h, the probability of one event e is (r_eh+o(h)), while the probability of two or more events is (o(h)). Therefore
\[
  \frac{\mathbb E_x[f(X_h)]-f(x)}h
   \longrightarrow \sum_e r_e(f(T_e(x))-f(x))=(Lf)(x).
\]
On a finite state space, boundedness makes this derivative calculation uniform in x. The semigroup therefore solves the finite Kolmogorov equation with generator L. One can alternatively identify the construction with the uniformized kernel mixture and appeal to the finite matrix exponential.

In Lean, the event-map model avoids beginning with a large transition matrix. Prove the local generator formula from one event, then sum over E. A separate theorem converts the event data to a matrix generator. That separation lets pathwise arguments use maps while semigroup arguments use matrices.

## 3. Marked diagrams and dependency neighborhoods

For a graph with vertex type V, an event type can include a site, an oriented edge, or a local mark. The event map then updates one coordinate or a bounded neighborhood. A space-time picture can be represented textually:

```text
time  ↑       site x       site y       site z
      │          │            │            │
  t₃ │          ● update     │            │
  t₂ │          │        ───▶ ● arrow      │
  t₁ │          ● mark        │            │
      └──────────────────────────────────────→ sites
```

An arrow from y to x means that the event at its mark transfers information from y to x; for a copying model, x adopts y’s current value. A mark can instead force a site to become occupied or vacant. The diagram is not a proof object, but its deterministic event interpretation often is: a finite list of marked events defines a composition of update maps.

The locality condition from Chapter 64 can be restated for event maps. If two configurations agree on the event’s dependency neighborhood, the event makes the same local change in both. This fact supports a coupled construction: expose the same event sequence to two initial configurations and compare their images after every mark.

## 4. Shared marks give a coupling

Let two initial configurations x and y evolve using the same clocks and the same event maps. The pair ((X_t,Y_t)) is a Markov chain on (Omega\times\Omega), with generator
\[
  (\widetilde L F)(x,y)=\sum_e r_e
    \bigl(F(T_e x,T_e y)-F(x,y)\bigr).
\]
Each marginal has generator L. This is a coupling by construction, not by a later existence theorem. If every update map contracts a chosen distance d, then (d(X_t,Y_t)) is nonincreasing along every event sequence. If certain marks force agreement, the same clocks can yield a coalescence bound.

More generally, two models may have different event maps but share a common part of their rates. Couple the common events and run the residual clocks independently. This is the graphical analogue of maximal or rate-splitting couplings. In a formal proof, state the decomposition (r_e=r_e^{\mathrm{common}}+r_e^{\mathrm{residual}}) as nonnegative data and verify both marginals by summing the coupled generator over the unused coordinate.

The shared-clock construction is particularly useful for monotone systems. Let Ω carry a partial order, and suppose each T_e is monotone: (x\leq y\Rightarrow T_e(x)\leq T_e(y)). Starting from ordered states and sharing all marks preserves the order pathwise. This gives stochastic monotonicity of the transition semigroup and can imply comparison of hitting times or expectations of increasing observables.

## 5. Worked example: the voter model

Let G be a finite graph and let a configuration be η:V→{0,1}. For each ordered neighboring pair (x,y), place an arrow (y\to x) at rate (c(x,y)\geq0). At an arrow, site x copies the value at y. The event map is
\[
  T_{x\leftarrow y}(\eta)=\eta[x\mapsto\eta(y)].
\]
The generator on observables is
\[
  (Lf)(\eta)=\sum_{x}\sum_{y\sim x}c(x,y)
       \bigl(f(T_{x\leftarrow y}\eta)-f(\eta)\bigr).
\]
The rate c need not be symmetric for the process definition, though symmetric rates have additional reversibility properties in related models.

The graphical construction also yields a dual process. To determine the value at site x at time t, trace backward from (x,t). When the path crosses an arrow pointing into its current site, it jumps backward to the arrow’s source. If two backward paths meet, they coalesce and share the same ancestral value. Thus a finite set of queried spins at time t is determined by a coalescing system of backward random walks started from those sites.

For (A\subseteq V), define (D(\eta,A)=\prod_{x\in A}\eta(x)), with the empty product one. The duality identity is
\[
  \mathbb E_\eta[D(\eta_t,A)]
    =\mathbb E_A[D(\eta,\xi_t)],
\]
where ξ is the coalescing walk system run backward from A. The left side asks whether every queried site is occupied by a 1 at time t; the right side asks whether every ancestor at time zero had value 1. The identity follows pathwise from arrow tracing, then expectation preserves equality.

For formalization, first define a single ancestral path from a fixed finite marked-event list, then prove the evaluation lemma by induction over the list length. Coalescence requires quotienting duplicate ancestors or representing the set of active paths as a finite set. The graphical statement is often simpler than deriving duality from generator algebra, while the generator identity provides an independent check.

## 6. Worked example: the contact process

The contact process uses configurations η:V→{0,1}, where 1 marks an infected site. At each site x, a recovery mark occurs at rate δ and forces x to 0. Along each oriented edge (y\to x), an infection arrow occurs at rate λ c(x,y); if y is infected, it forces x to 1. The generator is
\[
  (Lf)(\eta)=\delta\sum_x\bigl(f(\eta^{x,0})-f(\eta)\bigr)
   +\lambda\sum_{x,y:\,y\sim x}c(x,y)\eta(y)
       \bigl(f(\eta^{x,1})-f(\eta)\bigr).
\]
The event maps are monotone in the coordinatewise order. A recovery map sets the same coordinate to zero in both coupled systems; an infection map sets it to one if the source is infected and otherwise does nothing. Thus the common graphical construction preserves inclusion of infected sets.

On a finite graph, the all-zero configuration is absorbing and eventually reached with probability one when δ>0. A direct proof uses a finite sequence of recovery marks with no infection arrows during a fixed interval; this event has positive probability uniformly over configurations. Repeating over intervals gives a geometric tail for extinction time. The bound may be very small as the graph grows, so it does not by itself imply a useful infinite-volume extinction theorem.

This example distinguishes a pathwise monotonicity proof from a stationary-measure proof. The contact process is not reversible under a simple product law in general. Its useful order structure comes from the event maps, even when detailed balance is unavailable.

## 7. Finite constructions and infinite-volume limits

For finite V, the total event rate is the finite sum of all site and edge rates. The number of marks on a bounded time interval is almost surely finite, and every path is a finite composition. This gives a direct route to a process construction and avoids delicate explosion questions.

For an infinite locally finite graph, every site has finitely many incident clocks but the total number of marks in the whole graph is infinite in every time interval. A path at a fixed site can still be defined by tracing dependencies backward, provided the backward influence cluster remains finite on bounded time intervals. Proving this requires a domination argument, often by a branching process. The finite-volume chapter does not supply that limit theorem automatically.

A common approximation takes an increasing sequence of finite subgraphs and couples all finite systems with the same marks inside their domains. To prove convergence on a fixed finite observation window, show that marks outside a sufficiently large region cannot influence the observation with high probability. This is a finite-propagation estimate, not merely pointwise consistency. In Lean, keep the finite process, the exhaustion, and the influence event as separate definitions so that a later limit theorem can be stated cleanly.

## 8. Formalization architecture

A reusable event system can be represented by:

1. a finite type E of event labels;
2. a rate function (r:E\to\mathbb R_{\geq0});
3. an update map (T:E\to\Omega\to\Omega);
4. optional locality, monotonicity, or conservation predicates on T.

The deterministic algebraic core proves the generator formula, the row-sum identity, and marginalization of shared-event couplings. A probabilistic layer equips each event with a Poisson clock and proves the path law has this generator. Model-specific chapters instantiate the event type and maps. This division allows one theorem about random maps to serve voter, contact, spin-flip, and resampling systems.

Some proof obligations are easy to miss. If event labels include oriented edges, two labels may encode the same update map; they are still distinct clock types, and their rates add. If a no-op event occurs, it may be omitted from the state-jump chain but not from a particular graphical representation. If rates depend on the current state, use a dominating clock and state-dependent acceptance marks; fixed independent Poisson clocks apply directly only to fixed event rates.

## 9. Common failure modes

### A local event is mistaken for a unique transition

Different event labels can send the same state to the same destination. Sum all their rates when building the matrix.

### A no-op mark is treated as a state jump

The mark belongs to the graphical construction, but the configuration remains unchanged. Keep event rate distinct from exit rate.

### A coupling uses different clocks by accident

Pathwise order preservation depends on exposing the same marks and applying monotone maps to both states.

### Infinite volume is inferred from finite volume

Finite total rate fails on an infinite graph. A local dependency-cluster estimate is needed to define the limit.

### State-dependent rates are assigned fixed clocks without thinning

Use a dominating rate and acceptance mechanism, or define a state-dependent jump construction explicitly.

## 10. Event clocks and competing hazards

Independent clocks are convenient for a fixed finite event list, but they are not the only way to realize the same generator. At a state x, group all events that change the state and let (q(x,y)) be their total rate to y. The next genuine jump has an exponential waiting time with parameter (q(x)=\sum_{y\ne x}q(x,y)), and its destination is y with probability (q(x,y)/q(x)). This competing-hazards description forgets null events and is the usual jump-chain representation.

The event-clock and jump-chain constructions have the same law for the state process, though they retain different information. A graphical construction remembers which event label caused a change, which is essential for tracing ancestry or coupling updates. The jump chain remembers only the destination state and is often smaller for finite matrix calculations. Formalizing the map from event labels to destination rates makes this relationship precise: sum rates over each fiber of (e\mapsto T_e(x)), discard the fiber mapping to x, and leave the diagonal as minus the remaining total.

This distinction also clarifies state-dependent clocks. A fixed dominating Poisson clock can propose an event and accept it with a state-dependent probability. Rejected proposals are null marks. The accepted event rates reproduce the desired hazards, while the common dominating clock still supports a pathwise coupling of different initial states.

## 11. Exercises

1. Derive the generator from finitely many event maps and prove constants are annihilated.
2. Show that the uniformized construction has the same generator as independent event clocks.
3. Prove that common event maps define a coupling with the prescribed marginals.
4. Formalize the coordinatewise monotonicity of voter and contact-process event maps.
5. Trace a two-site voter-model ancestry through a fixed finite list of arrows.
6. Prove the voter duality identity for a finite set A by induction on the number of marks.
7. Give a positive-probability event that guarantees contact-process extinction on a finite graph during a fixed time interval.
8. Explain how two event labels that induce the same transition contribute to the generator matrix.
9. State a graphical construction for a spin-flip system with configuration-dependent rates using dominating clocks.
10. Identify a finite-propagation estimate needed to pass from finite subgraphs to an infinite graph.

## Summary

A finite interacting system can be constructed from event rates and deterministic update maps. Independent Poisson clocks produce chronological compositions whose generator is a sum of local increments. Sharing marks couples two initial states and turns monotonicity of maps into pathwise order preservation. Voter arrows also encode coalescing ancestral paths and a duality identity; contact-process marks provide a monotone infection coupling. The finite construction is rigorous with finitely many event types, while infinite-volume limits require additional control of backward influence.

## Further reading

- Chapters 56, 62, and 64 for uniformization, coupling, and local configuration generators.
- [Mathlib’s finite simple-graph API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Finite.html).
- [Mathlib’s simple-graph connectivity API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.html).

## 12. Lean formalization: finite mark sequences and shared clocks

The finite pathwise core of a graphical construction is a list of event labels. Once that list is fixed, the path is deterministic: fold the corresponding update maps over the initial state in chronological order. We formalize this finite trace separately from the Poisson process that samples the marks. The separation keeps the induction arguments about paths elementary while making clear that probability laws and infinite-volume limits require additional theorems.

The two-state example from the supplemental module is recorded here as executable Lean. Two successive flips return every state to its starting value; the proof uses computation because the state space is finite.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def eventFlip (s : State) : State := if s = zero then one else zero
def applyTwoEvents (s : State) : State := eventFlip (eventFlip s)

theorem twoIdenticalEventsCancel : applyTwoEvents zero = zero := by decide
```

For a general event type, `applyEvents` evaluates an ordered list of marks. The cons equation exposes the first update, which is the useful induction principle: prove an invariant for the one-step map, then propagate it through the remaining trace.

```lean
def applyEvents {Ω Event : Type} (update : Event → Ω → Ω)
    (events : List Event) (initial : Ω) : Ω :=
  events.foldl (fun state event => update event state) initial

theorem applyEvents_cons {Ω Event : Type} (update : Event → Ω → Ω)
    (event : Event) (events : List Event) (initial : Ω) :
    applyEvents update (event :: events) initial =
      applyEvents update events (update event initial) := by
  rfl

theorem applyEvents_append {Ω Event : Type} (update : Event → Ω → Ω)
    (first second : List Event) (initial : Ω) :
    applyEvents update (first ++ second) initial =
      applyEvents update second (applyEvents update first initial) := by
  induction first generalizing initial with
  | nil => rfl
  | cons event first ih =>
      rw [List.cons_append, applyEvents_cons, ih, applyEvents_cons]

theorem applyEvents_monotone {Ω Event : Type} [Preorder Ω]
    (update : Event → Ω → Ω)
    (preservesOrder : ∀ event, Monotone (update event))
    (events : List Event) : Monotone (applyEvents update events) := by
  induction events with
  | nil =>
      intro x y hxy
      exact hxy
  | cons event events ih =>
      intro x y hxy
      rw [applyEvents_cons, applyEvents_cons]
      exact ih (preservesOrder event hxy)

def applySharedMarks {Ω Event : Type} (update : Event → Ω → Ω)
    (events : List Event) (initial : Ω × Ω) : Ω × Ω :=
  events.foldl
    (fun pair event => (update event pair.1, update event pair.2)) initial

theorem applySharedMarks_fst {Ω Event : Type}
    (update : Event → Ω → Ω) (events : List Event) (x y : Ω) :
    (applySharedMarks update events (x, y)).1 =
      applyEvents update events x := by
  induction events generalizing x y with
  | nil => rfl
  | cons event events ih =>
      change
        (applySharedMarks update events
          (update event x, update event y)).1 =
        applyEvents update events (update event x)
      exact ih (update event x) (update event y)

theorem applySharedMarks_snd {Ω Event : Type}
    (update : Event → Ω → Ω) (events : List Event) (x y : Ω) :
    (applySharedMarks update events (x, y)).2 =
      applyEvents update events y := by
  induction events generalizing x y with
  | nil => rfl
  | cons event events ih =>
      change
        (applySharedMarks update events
          (update event x, update event y)).2 =
        applyEvents update events (update event y)
      exact ih (update event x) (update event y)

theorem applySharedMarks_preservesOrder {Ω Event : Type} [Preorder Ω]
    (update : Event → Ω → Ω)
    (preservesOrder : ∀ event, Monotone (update event))
    (events : List Event) (x y : Ω × Ω)
    (h₁ : x.1 ≤ y.1) (h₂ : x.2 ≤ y.2) :
    (applySharedMarks update events x).1 ≤
        (applySharedMarks update events y).1 ∧
      (applySharedMarks update events x).2 ≤
        (applySharedMarks update events y).2 := by
  rw [applySharedMarks_fst, applySharedMarks_fst,
    applySharedMarks_snd, applySharedMarks_snd]
  exact ⟨applyEvents_monotone update preservesOrder events h₁,
    applyEvents_monotone update preservesOrder events h₂⟩
```

The projection theorems say that each coordinate of the coupled trace is exactly the corresponding one-system trace; this is the deterministic marginal property behind the shared-clock coupling. The order theorem is pathwise: if every update preserves the order, then applying the same mark list to ordered initial states preserves the order at every prefix, and therefore at the end. These results formalize the finite event algebra, not the claim that Poisson sampling has the specified generator; that probabilistic step remains a separate semigroup argument from Section 2.
