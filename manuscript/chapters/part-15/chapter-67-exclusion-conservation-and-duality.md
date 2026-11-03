# Chapter 67 — Exclusion, Conservation, and Duality

> **Audience.** This chapter assumes finite interacting particle systems, generator calculations, detailed balance, and the graphical viewpoint from Chapter 66. It studies the symmetric exclusion process on a finite graph and uses its conservation law to organize state spaces, stationary measures, and duality proofs.

In an exclusion process, particles move along graph edges but cannot occupy the same site. The local rule is simple: an occupied site exchanges its state with a vacant neighbor. Its consequences are structural. The total particle count is conserved, the configuration space splits into communicating sectors, and natural invariant distributions appear by conditioning product measures on those sectors. The generator also acts on products of occupation variables as the generator of a smaller exclusion process, giving a useful self-duality.

These facts make exclusion a model example for formalizing a process with nontrivial constraints. The key is to distinguish properties of a single update from properties of the global state space, and to prove the generator identities before invoking semigroups.

## Learning objectives

By the end of this chapter, you should be able to:

- define the symmetric exclusion generator using coordinate swaps;
- prove particle number is preserved and restrict dynamics to fixed-count sectors;
- establish reversibility of uniform canonical and Bernoulli product measures;
- derive the one-particle random-walk equation for occupation expectations;
- state and prove the finite-set self-duality identity;
- design Lean interfaces for constrained configuration spaces.

## 1. Configurations and exchanges

Let G be a finite undirected graph with vertex type V. A configuration is η:V→{0,1}; value 1 means occupied and value 0 means vacant. For distinct vertices x,y, write η^{xy} for the configuration obtained by swapping η(x) and η(y), leaving all other coordinates fixed. If the values agree, this swap does not change the configuration.

Assign a symmetric nonnegative rate c(x,y)=c(y,x) to each adjacent pair and rate zero to nonedges. An oriented description of the generator sums over ordered pairs:
\[
  (Lf)(\eta)=\sum_{x,y\in V}c(x,y)\eta(x)(1-\eta(y))
       \bigl(f(\eta^{xy})-f(\eta)\bigr).
\]
Only an occupied-to-vacant move contributes. Because c is symmetric, summing ordered pairs is convenient: each legal particle jump has a source and a destination, and the reverse move appears as a separate summand from the swapped state. One may instead sum once over unordered edges, using a single exchange term; the two formulas agree after pairing orientations.

The rate (c(x,y)) is attached to an attempted directed move from x to y. Symmetry makes the reverse edge rate equal. The total exit rate from η is finite and at most ∑_{x,y} c(x,y), so the finite-state process is non-explosive.

## 2. The particle-count conservation law

Define the particle number (N(\eta)=\sum_x\eta(x)). Every update swaps two values, so (N(\eta^{xy})=N(\eta)). Consequently, the process remains in the level set
\[
  \Omega_k=\{\eta:V\to\{0,1\}:\sum_x\eta(x)=k\}
\]
for all time when it starts in Ω_k. The full configuration space is a disjoint union of these invariant sectors.

There are two formal proof routes. The local route proves the swap preserves the sum by separating x,y from all other vertices. The generator route establishes (LN=0), which implies (N(X_t)) is a martingale; because every jump preserves N pointwise, it is in fact constant pathwise. The first route is stronger and shorter for conservation. The generator identity is useful as a pattern for conserved quantities that are not literally unchanged by each event but have zero conditional drift.

For an update-map representation from Chapter 66, define the event map by swapping x and y. Its preservation theorem can be placed in the event-system type as an invariant predicate. The stochastic process then inherits the sector restriction automatically. This is preferable to proving from scratch for each time t that a trajectory started in Ω_k remains there.

## 3. Invariant canonical measures

Assume the graph of positive rates is connected. Within each sector Ω_k, consider the uniform probability measure. The generator is reversible with respect to this law. Indeed, if η' is obtained from η by a legal move along edge {x,y}, then η' is in the same sector, the two configurations have equal mass, and the reverse move has the same rate c(x,y). If two configurations are not related by one legal move, their one-step rates in both directions are zero. Thus pairwise detailed balance holds.

The uniform measure on Ω_k is stationary even if the graph is disconnected, but then Ω_k may split into smaller communicating classes according to particle count in each connected component. Connectivity of the graph ensures that any two k-particle configurations can be connected by legal moves, so the sector chain is irreducible. The proof uses the fact that particles can be transported along paths while vacancies move in the opposite direction. Boundary sectors k=0 and k=|V| contain only one state.

A common formal mistake is to show the full chain is irreducible. It cannot be when there is more than one possible particle count. State irreducibility on the subtype or finite set Ω_k. If developing the transition kernel on all configurations, express the result as irreducibility after restricting to the invariant sector.

## 4. Product Bernoulli measures and mixtures

Fix (0<\rho<1). Give each site an independent Bernoulli(ρ) occupation variable. The probability of η is
\[
  \nu_\rho(\eta)=\rho^{N(\eta)}(1-\rho)^{|V|-N(\eta)}.
\]
This law is reversible for symmetric exclusion: an exchange preserves particle count, hence preserves the configuration’s probability; the move rate equals its reverse rate. Therefore detailed balance holds term by term.

The product law is a mixture of the canonical uniform laws. Conditional on (N(\eta)=k), every k-particle configuration has the same Bernoulli probability, so
\[
  \nu_\rho=\sum_{k=0}^{|V|}\Pr_{\nu_\rho}(N=k)\,U_k,
\]
where U_k is uniform on Ω_k. This identity relates a family of sector-invariant laws to a grand-canonical stationary law. It is also a useful formal proof strategy: establish invariance for each sector, then combine using a finite mixture.

Conversely, the count N is a complete statistic for the mixture components. Conditioning on N=k removes the parameter ρ, yielding the canonical law. In Lean, this can be handled with a finite distribution over `Finset V` or a probability measure on the finite function type. A bijection between 0–1-valued functions and finite subsets often simplifies the combinatorics, while coordinate functions make the generator calculation easier. Define the equivalence once and move between representations only at theorem boundaries.

## 5. Worked example: two particles on a four-cycle

Take V={0,1,2,3} with cycle edges and unit rates. The k=2 sector has six configurations, corresponding to the six two-element subsets of V. The uniform law assigns mass 1/6 to each. A configuration with adjacent particles has two legal moves; one with opposite particles has four. These different exit rates do not obstruct stationarity: detailed balance compares each edge of the configuration graph separately, not the total rate at each vertex.

For example, the configuration {0,1} can move to {0,3} by the particle at 1 jumping to 3, and to {1,2} by the particle at 0 jumping to 2. The reverse rates are both one. Directly listing the six states verifies every row of the generator sums to zero and every pair of neighboring states has equal stationary flow.

This small example is useful for catching mistaken arguments that infer stationarity from equal exit rates. Stationary distributions need not assign equal total outgoing rate at every state; incoming flows balance them. The uniform law works here because each allowed configuration-space edge has a reverse edge of equal rate and each vertex mass is equal.

## 6. Occupation expectations and the one-particle walk

For a fixed site x, apply the generator to the coordinate observable (f_x(\eta)=\eta(x)). Pair contributions along each edge to obtain
\[
  (Lf_x)(\eta)=\sum_y c(x,y)(\eta(y)-\eta(x)).
\]
Thus the expected occupation (m_t(x)=\mathbb E[\eta_t(x)]) solves the linear heat equation on the weighted graph:
\[
  \frac{d}{dt}m_t(x)=\sum_y c(x,y)(m_t(y)-m_t(x)).
\]
The many-particle interactions disappear from this first-moment equation. The exclusion constraint is still present pathwise, but its effect cancels in the drift of a single occupation variable.

The same cancellation does not imply that the entire process is a collection of independent random walks. Joint moments depend on exclusion interactions, and two particles cannot occupy the same site. The equation closes for first moments, while higher-order observables lead to a k-particle exclusion process, as the duality theorem makes precise.

In Lean, prove the generator identity by splitting the ordered-edge sum into terms where x is the source, destination, or neither. `Finset.sum_erase_add` or a reindexing by neighbors can express the cancellation. Once established, the expectation equation follows from the finite-state semigroup derivative theorem; no stochastic independence assumption is needed.

## 7. Self-duality on finite subsets

For a finite subset A⊆V, define the monomial observable
\[
  D(\eta,A)=\prod_{x\in A}\eta(x).
\]
It equals one exactly when every site of A is occupied. Let (A_t) evolve as a k-particle exclusion process with the same edge rates: a particle in A moves from x to y when x∈A and y∉A. Then the symmetric exclusion process satisfies
\[
  \mathbb E_\eta[D(\eta_t,A)]=\mathbb E_A[D(\eta,A_t)].
\]
This is self-duality. It says that an expectation of a k-site product in the original process can be computed by running k dual particles from A and evaluating the initial configuration on their positions.

The algebraic core is a generator identity. For fixed A and an edge {x,y}, there are three cases. If neither endpoint is in A, the monomial is unaffected. If exactly one endpoint is in A, exchanging occupations changes the monomial just as moving the dual particle across the edge changes A. If both endpoints lie in A, the product η(x)η(y) is invariant under the swap, and the dual configuration has no legal move along that edge. Summing these cases gives (L_\eta D(\eta,A)=L_A D(\eta,A)).

On a finite state space, equality of these generator actions implies equality of semigroup actions. Define the dual semigroup on subsets of fixed cardinality and use the finite-dimensional ODE uniqueness theorem. This route is often easier to formalize than comparing pathwise constructions, though the graphical construction gives the most intuitive explanation. The best development proves both the local generator identity and the semigroup intertwining theorem once.

## 8. A comparison with voter duality

The voter-model dual from Chapter 66 also traces backward paths, but its dual particles coalesce when they meet. Exclusion dual particles instead repel in the sense that a move onto an occupied dual site is suppressed. The distinction reflects the forward update: voter sites copy values, while exclusion sites exchange occupations.

Both dualities have the same abstract shape. There are state spaces Ω and Δ, a pairing (D:\Omega\times\Delta\to\mathbb R), and generators satisfying
\[
  L_\Omega D(\cdot,\delta)(\eta)
   =L_\Delta D(\eta,\cdot)(\delta).
\]
The semigroup identity follows from this intertwining relation. A reusable Lean theorem can package finite state spaces, two generators, a pairing, and this generator identity, then derive duality without knowing whether Δ describes coalescing walks, exclusion particles, or another process.

## 9. Formalizing sector measures

There are several equivalent representations for configurations:

- functions (V\to\mathrm{Bool}), convenient for coordinate updates;
- finite subsets of V, convenient for particle count and the dual;
- a subtype of functions with a fixed finite sum, convenient for sector chains.

The equivalence between Boolean-valued functions and finite subsets preserves occupation sums as cardinalities. Prove that the exchange map corresponds to removing one endpoint and inserting the other when the source is occupied and destination empty. This gives a clean bridge between configuration updates and finite-set combinatorics.

For the uniform canonical measure, define it as normalized counting measure on Ω_k. To avoid repeating normalization proofs, first establish that the sector is nonempty for (0\leq k\leq |V|), then use a generic finite counting measure. Detailed balance is a pairwise theorem about a move and its inverse. Stationarity follows by summing the pairwise identity, so the proof does not need to count incoming neighbors separately.

For self-duality, keep the dual state type as `Finset V` with a cardinality invariant or as a subtype. The subtype makes the fixed k state space explicit but may complicate update lemmas; the unrestricted finite-set type simplifies the definition while the generator automatically preserves cardinality. Choose based on downstream API needs and prove cardinality preservation either way.

## 10. Common failure modes

### Irreducibility is claimed on the full configuration space

Particle count is conserved, so irreducibility belongs to a fixed-count sector.

### Uniform stationarity is justified by equal exit rates

Exit rates can vary across configurations. Use detailed balance along each configuration-space edge.

### Directed terms are double-counted

An unordered edge contributes two possible directed particle moves, but only one is legal in a given 10/01 configuration. State whether the sum is over ordered or unordered pairs.

### The dual process is confused with independent walks

Dual particles obey exclusion: a jump to an occupied site is suppressed. The product observable encodes this interaction.

### A first-moment equation is mistaken for full independence

The drift of one coordinate closes, but joint laws remain interacting.

## 11. Sector Dirichlet forms and mixing

On a fixed sector Ω_k, the uniform stationary law and reversible generator give a finite Dirichlet form. For a real observable F on configurations,
\[
  \mathcal E_k(F,F)=\frac12\sum_{\eta\in\Omega_k}U_k(\eta)
     \sum_{x,y}c(x,y)\eta(x)(1-\eta(y))
       (F(\eta^{xy})-F(\eta))^2.
\]
This is the energy on the configuration graph: its vertices are k-particle configurations, and two vertices are joined when one legal particle jump relates them. The underlying spatial graph controls which configuration edges exist, but the spectral gap is a property of the larger configuration graph.

For connected G and (0<k<|V|), irreducibility makes constants the only zero-energy observables. The sector spectral gap is therefore the best λ such that λ Var_{U_k}(F) ≤ ℐ_k(F,F) for all F. A comparison proof can map long configuration moves to paths of legal edge moves and bound congestion. Such estimates are a gateway to mixing-time results, but their constants may depend on both the graph geometry and particle density.

The one-particle sector k=1 is exactly the weighted random walk from Chapter 65. Higher sectors introduce exclusion constraints, and their gap need not be read off from the spatial Laplacian without an additional theorem. In Lean, define the finite sector type and its uniform measure first; then reuse the reversible Dirichlet-form API rather than rebuilding spectral theory inside the particle-system development.

## 12. Exercises

1. Prove that a coordinate swap preserves the total particle count.
2. Derive the generator on the particle-number observable and show it is zero.
3. Prove detailed balance for the uniform distribution on a fixed-k sector.
4. Show that Bernoulli(ρ) product measure is a mixture of canonical uniform laws.
5. Verify stationarity in the two-particle four-cycle example by listing configuration edges.
6. Derive the discrete graph heat equation for the expected occupation at a site.
7. Prove the self-duality generator identity for a monomial (D(\eta,A)).
8. Explain how connectivity of the graph implies irreducibility within Ω_k.
9. Formalize the equivalence between Boolean configurations and finite subsets.
10. Compare the dual particle rules for voter and exclusion models.

## Summary

The symmetric exclusion process moves particles by exchanging occupied and vacant neighboring sites. Each event preserves the total count, splitting the configuration space into invariant sectors. Symmetric rates give detailed balance for the uniform law on each sector and for Bernoulli product measures; the latter are mixtures of canonical laws. First moments evolve by the weighted graph heat equation. Products of occupation variables satisfy a generator intertwining identity with a k-particle exclusion process, yielding self-duality. In Lean, coordinate swaps, fixed-count state types, and pairwise flow balance are the central reusable components.

## Further reading

- Chapters 64–66 for local generators, graph energy, and graphical constructions.
- [Mathlib’s finite graph edge and neighbor API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Finite.html).
- [Mathlib’s finite graph connectivity API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.html).

## 13. Lean formalization: conservation and one-site duality

The first formal model is a single edge with two sites. An event swaps the two Boolean occupations. This tiny system isolates two algebraic facts that scale to a finite graph: particle number is unchanged by an exchange, and the generator applied to the occupation at one site agrees with the generator of a single dual walker. The general finite-graph proofs require a finite sum over edges, but their local step is exactly the identity checked here.

The supplemental numeric example is kept as a simple executable calculation. The following model strengthens it from one input to all configurations of the two-site system.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def exchangeOccupancies (a b : Nat) : Nat × Nat := (b, a)
def particleCount (p : Nat × Nat) : Nat := p.1 + p.2

theorem exclusionMoveConservesParticles :
    particleCount (exchangeOccupancies 1 0) = particleCount (1, 0) := by decide
```

The update is an involution, so its event map is the same in the forward and reverse directions. An event with equal occupations is a null mark. We encode the single-edge generator as the rate-one increment `f (swapConfig η) - f η`; when the update is a null mark, that increment is zero automatically.

```lean
inductive ExclusionSite where
  | left
  | right
  deriving DecidableEq

abbrev ExclusionConfig := ExclusionSite → Bool

def swapSite : ExclusionSite → ExclusionSite
  | .left => .right
  | .right => .left

def swapConfig (η : ExclusionConfig) : ExclusionConfig :=
  fun site => η (swapSite site)

def siteParticleCount (η : ExclusionConfig) : Int :=
  (if η .left then 1 else 0) + (if η .right then 1 else 0)

theorem swapConfig_involutive (η : ExclusionConfig) :
    swapConfig (swapConfig η) = η := by
  funext site
  cases site <;> rfl

theorem swapConfig_conserves_particles (η : ExclusionConfig) :
    siteParticleCount (swapConfig η) = siteParticleCount η := by
  cases hLeft : η .left <;> cases hRight : η .right <;>
    simp [siteParticleCount, swapConfig, swapSite, hLeft, hRight]

def exclusionGenerator (observable : ExclusionConfig → Int)
    (η : ExclusionConfig) : Int :=
  observable (swapConfig η) - observable η

theorem exclusionGenerator_annihilates_particleCount (η : ExclusionConfig) :
    exclusionGenerator siteParticleCount η = 0 := by
  simp [exclusionGenerator, swapConfig_conserves_particles]

def occupationAt (site : ExclusionSite) (η : ExclusionConfig) : Int :=
  if η site then 1 else 0

def oneParticleGenerator (observable : ExclusionSite → Int)
    (site : ExclusionSite) : Int :=
  observable (swapSite site) - observable site

theorem oneSiteGenerator_duality (η : ExclusionConfig)
    (site : ExclusionSite) :
    exclusionGenerator (fun config => occupationAt site config) η =
      oneParticleGenerator (fun position => occupationAt position η) site := by
  rfl
```

The conservation proof reduces to the two occupancy cases and shows the local update preserves the sector exactly, not merely in expectation. The duality theorem identifies the action of the exclusion generator on a one-site occupation with the walk generator acting on the site variable while the initial configuration is held fixed. The two-site model is a regression example for the local algebra; extending it to all edges and finite subsets requires summing these local identities and proving the corresponding semigroup intertwining theorem.
