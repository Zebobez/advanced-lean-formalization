# Chapter 64 — Product Generators and Local Interactions

> **Audience.** This chapter assumes the finite-state continuous-time framework from Chapters 55–60 and the conditional-update viewpoint from Chapter 50. Its goal is to formalize systems whose state is a configuration of many finite components.

Many stochastic models have a large state space for a simple reason: the state records one value at every site, coordinate, or particle. A system with n binary sites has (2^n) configurations, but each event may change only one coordinate. Treating its generator as an arbitrary (2^n\times2^n) matrix erases this structure. Product generators and local-update formulas preserve it, making proofs both shorter and more reusable.

The chapter first builds the finite configuration-space generator, then separates independent products from genuine interactions. Two-spin heat-bath dynamics provide a small interacting example in which the local rate formula, detailed balance, and the Gibbs distribution can all be checked by hand.

## Learning objectives

By the end of the chapter, you should be able to:

- define a finite-state generator on configurations of local variables;
- express independent dynamics as a sum of coordinate generators;
- identify when product transition semigroups and stationary laws follow;
- distinguish commuting independent terms from noncommuting interacting terms;
- formalize coordinate replacement and local rates without obscuring boundaries;
- verify detailed balance for a finite heat-bath system.

## 1. Configurations and coordinate replacement

Let V be a finite set of sites and E a finite set of local states. A configuration is a function η : V → E, so the configuration space is the function type (E^V). For a site v and a proposed new state a, define η[v ↦ a] to agree with η away from v and to have value a at v. In Lean this is naturally expressed using function update; it is useful to prove once that updating a coordinate leaves every other evaluation unchanged and sets the selected coordinate to a.

Suppose the rate of replacing the value at v by a is (c_v(η,a)geq0). The generator on a real-valued observable f is
\[
  (Lf)(\eta)=\sum_{v\in V}\sum_{a\ne\eta(v)}
  c_v(\eta,a)\bigl(f(\eta[v\mapsto a])-f(\eta)\bigr).
\]
Each summand has the standard rate-times-increment form. This immediately gives (L1=0), because a constant observable has zero increment. It also gives the off-diagonal rates directly; the diagonal rate is minus the sum of all rates leaving the configuration.

The restriction (a\ne\eta(v)) avoids counting a null update as a jump. Alternatively, sum over all a and permit the current state with its own rate: its increment is zero, so the generator is unchanged. The first convention is better when defining a jump matrix; the second can simplify conditional-resampling formulas. Whichever convention is chosen, state it consistently in the definition of the total exit rate.

For finite V and E, the configuration space is finite. If every local rate is finite, the maximum total exit rate is finite, so the generator defines a non-explosive continuous-time chain. No infinite-volume argument is hidden in this setup. The formal proof can construct a finite matrix or work directly with the displayed action formula.

## 2. Independence and coordinate generators

For independent sites, the rate for changing site v depends only on its current value and the proposed new value. Write this rate as (q_v(x,a)). Then
\[
  (Lf)(\eta)=\sum_{v\in V}\sum_{a\ne\eta(v)}q_v(\eta(v),a)
  \bigl(f(\eta[v\mapsto a])-f(\eta)\bigr).
\]
The contribution for each v is the one-coordinate generator applied in the v-th slot while all other coordinates are held fixed. Thus L is the sum of coordinate operators. This sum is sometimes called a Kronecker sum when the state spaces and matrices are explicitly enumerated.

For two components with generators (Q_1) and (Q_2), a function F on the product has generator
\[
  (QF)(x,y)=\sum_{x'}Q_1(x,x')F(x',y)
           +\sum_{y'}Q_2(y,y')F(x,y').
\]
In matrix notation this is (Q_1\otimes I+I\otimes Q_2), subject to the library’s convention for row-versus-column actions. The formula on functions is the safest reference point: it fixes which coordinate changes and prevents transposition errors.

When the two coordinate generators are independent, their lifted operators commute. Therefore their semigroup factors:
\[
  e^{t(Q_1\otimes I+I\otimes Q_2)}
   =e^{tQ_1}\otimes e^{tQ_2}.
\]
If π1 and π2 are stationary laws for the factors, their product is stationary for the joint generator. Under reversibility, the product law is reversible as well. For irreducible reversible factors with positive spectral gaps, the product chain has gap equal to the minimum of the component gaps. The slowest coordinate controls the long-time rate.

These conclusions rely on separability, not merely on the fact that the state space is a product. A model can live on (E^V) and still have interacting rates that depend on neighboring values. Product state space is a representation; independence is an additional property of the generator.

## 3. Worked example: two independent two-state components

Take two sites with state space ({0,1}). Site i flips from 0 to 1 at rate α_i and from 1 to 0 at rate β_i, with both rates positive. Its stationary probability of 1 is (p_i=\alpha_i/(\alpha_i+\beta_i)). The joint state space contains ((0,0),(0,1),(1,0),(1,1)). Only one coordinate changes in any jump.

The joint stationary mass is the product of the two Bernoulli laws. To check detailed balance for an edge that flips site 1, fix the value y of site 2. The ratio of the two endpoint masses is (p_1/(1-p_1)=\alpha_1/\beta_1), exactly the ratio of the forward and reverse rates. Edges that flip site 2 are checked in the same way. There are no transitions changing both sites at once, so all other off-diagonal detailed-balance equations have zero on both sides.

This four-state example is a good sanity check for the matrix assembly. The diagonal entry at ((x,y)) is the negative sum of the two possible coordinate-flip rates. Every row must sum to zero. The matrix action should agree with the coordinate formula for an arbitrary F, not merely for a selected test function.

The system also illustrates a formalization tradeoff. Enumerating four states makes `decide` and finite case splitting effective, but obscures the proof’s scaling to n sites. A reusable theorem should quantify over the component type and prove the product result abstractly; finite enumeration is best reserved for small examples and executable checks.

## 4. Interactions and local dependence

An interacting system keeps the same coordinate-update shape but permits (c_v(\eta,a)) to depend on the neighborhood of v. For a graph (G=(V,E_G)), a common assumption is that the rate at v depends only on η(v) and values at neighbors of v. This is locality: changing a distant coordinate does not affect the immediate update rate at v.

Locality should be expressed as an extensional invariance statement. If configurations η and ξ agree on the dependency neighborhood of v, then (c_v(\eta,a)=c_v(\xi,a)). This statement is more robust than baking a graph lookup into every proof. It supports later arguments about disjoint regions, finite propagation approximations, and couplings.

Although L is still a sum of local terms (L_v), the terms need not commute. If the update rate at v depends on the value at w, then applying an update at w can change the rate used by (L_v). Consequently, in general,
\[
  e^{t\sum_v L_v}\ne\prod_v e^{tL_v}.
\]
A product of coordinate semigroups would describe a chosen sequential or split update scheme, not the original continuous-time process. Trotter-type approximations can relate the two, but require an additional limiting theorem. Formal developments should never infer factorization solely from an additive generator decomposition.

## 5. Worked example: two-spin heat-bath dynamics

Let each spin σ_i lie in ({-1,+1}), and let the energy of a pair be (H(\sigma)=-J\sigma_1\sigma_2). For inverse temperature β, the Gibbs law is
\[
  \pi(\sigma)=Z^{-1}\exp(\beta J\sigma_1\sigma_2),
  \qquad Z=4\cosh(\beta J).
\]
At rate κ_i>0, choose spin i for an update and resample it from its conditional Gibbs distribution. Given the other spin σ_j, the probability of setting spin i to s is
\[
  p_i(s\mid\sigma_j)=
  \frac{\exp(\beta J s\sigma_j)}{2\cosh(\beta J)}.
\]
Thus the transition rate from σ to the configuration with spin i set to s≠σ_i is κ_i p_i(s | σ_j). This is a local generator: a spin’s update depends only on its neighbor.

To verify detailed balance, compare configurations σ and σ' that differ only at site i. The joint Gibbs mass factors into the marginal weight of the other spin and the conditional probability of the current spin. Multiplying by the rate to choose σ'_i gives
\[
  \pi(\sigma)\,\kappa_i p_i(\sigma'_i\mid\sigma_j)
  =\kappa_i\pi(\sigma_{-i})
    p_i(\sigma_i\mid\sigma_j)p_i(\sigma'_i\mid\sigma_j),
\]
which is symmetric in σ_i and σ'_i. Hence it equals the reverse flow. Pairs differing at both sites have transition rate zero in both directions. The Gibbs law is therefore reversible and stationary.

When J=0, each conditional distribution is uniform and the two coordinate generators act independently. For nonzero J, an update at one site changes the conditional distribution used at the other; the generator terms interact. The stationary distribution still factorizes into edge-flow equalities, but the transition semigroup does not factor into two independent spin semigroups.

This example ties Chapters 49–50 to continuous time. Metropolis–Hastings modifies a proposal to preserve a target, while heat-bath dynamics draws directly from a conditional law. Both are proved by comparing flow along a transition and its reverse. The difference is the mechanism producing the transition rate, not the detailed-balance proof pattern.

## 6. Product stationary laws and reversibility

For independent components, let each factor have stationary law π_v and generator (L_v). The product measure π satisfies
\[
  \int Lf\,d\pi=\sum_{v\in V}\int L_vf\,d\pi=0.
\]
The first equality follows by finite-sum rearrangement and the product measure’s marginal property; the second follows from stationarity in coordinate v while other coordinates are fixed. For detailed balance, each local transition changes one coordinate, so the two configurations differ in exactly one factor and the factor’s reversible identity supplies the equality.

For an interacting model, the product law may fail to be stationary. It can still be a candidate in special cases, but the local edge equations must be checked with the configuration-dependent rates. A reliable proof strategy is to classify transitions by the updated site, establish pairwise flow balance for each class, and then sum. This avoids expanding the full configuration matrix.

For reversible independent factors, the product-space variance and Dirichlet form decompose in ways that yield the minimum-gap rule. A function depending only on a slow coordinate witnesses that the joint gap cannot exceed that factor’s gap. The tensor-product eigenbasis, or a variance decomposition by coordinates, gives the reverse inequality. In Lean, this is a substantial theorem: state the finite-dimensional spectral assumptions precisely and separate it from the simpler product-stationarity result.

## 7. Formalizing finite configurations

For a fixed finite site type V, `V → E` is often a better state representation than a hand-written tuple. It provides coordinate evaluation and function update uniformly for any number of sites. The finite configuration space follows from `Fintype V` and `Fintype E`. For explicit matrix calculations, an equivalence to `Fin (Fintype.card V)`-indexed encodings may be useful, but should be introduced only at the boundary to a matrix theorem.

The main lemmas for a coordinate update are uncomplicated but worth centralizing:

1. evaluation at the updated site returns the proposed value;
2. evaluation at any distinct site is unchanged;
3. two updates at distinct sites commute;
4. updating a site to its current value leaves the configuration unchanged.

The third lemma is particularly useful when proving independence and locality. It lets the proof rearrange updates without extensionality boilerplate. Conversely, when two updates target the same site, their order generally matters; the last update wins. A lemma that omits the distinct-site hypothesis can silently assert a false identity.

There are two reasonable definitions of the generator. A direct observable definition uses the local increment sum shown above and is pleasant for mathematical proofs. A matrix definition builds off-diagonal entries and sets each diagonal to the negative row sum; this integrates with finite-state semigroup APIs. Prove a single equivalence theorem between them. Subsequent analysis can then switch representation without repeatedly expanding matrix sums.

The proof dependencies are compact enough to keep visible while developing the API:

```text
configuration update lemmas ──> local observable generator ──> generator matrix
             │                            │                         │
             v                            v                         v
       locality facts              balance equations          semigroup API
                                          │
                            ┌─────────────┴─────────────┐
                            v                           v
                     stationary law              mixing/spectral results
```

This organization encourages a small core: coordinate updates and the observable generator are model-specific, while row sums, matrix equivalence, stationarity, and semigroup results can be shared across finite local systems.

## 8. Product matrices and library boundaries

Mathlib provides matrix Kronecker products and notation for the product-indexed construction. The exact type-level indexing matters: a matrix on α and one on β combines into a matrix on α × β, and identity factors preserve the untouched coordinate. Rather than memorizing an orientation-sensitive theorem name, first verify the action equation on a test function. Then use the Kronecker API theorem that matches that equation.

For continuous-time chains, the relevant algebraic identity is the exponential of a Kronecker sum. In a finite-dimensional space, it follows from commuting lifted operators and the exponential addition theorem. If the installed Mathlib version does not expose the exact matrix theorem needed, prove the operator identity by a power-series argument or use the finite-dimensional continuous-linear-map exponential interface. Avoid replacing the theorem with an unsupported statement that all matrix exponentials distribute over sums; they do not without commutation.

Transition kernels provide another representation. Independent one-step kernels combine by product, and composition gives iterated evolution. However, a continuous-time product generator is not the same thing as one simultaneous discrete-time update of every component. The distinction between kernel composition, product kernels, and a generator sum should remain visible in the definitions. Mathlib’s kernel composition interface can support the discrete transition side, while the finite matrix generator supplies the continuous-time side.

## 9. Common failure modes

### Product state space is mistaken for independence

Independence is a property of rates or generator terms. A neighbor-dependent rate creates interaction even on a Cartesian product.

### The diagonal is forgotten

Off-diagonal rates alone do not define a Markov generator. Set the diagonal to minus the outgoing-rate sum and prove every row sums to zero.

### Null updates are counted inconsistently

Including a current-state proposal is harmless for the observable formula, but it should not count as a genuine jump or inflate an exit rate.

### A Kronecker sum is assumed to exponentiate termwise

Factorization requires commuting lifted generators. Interacting local terms need not commute.

### Coordinate updates are reordered without distinctness

Updates at different sites commute; two updates to the same site do not. Keep the site inequality in the lemma statement.

### An infinite-volume theorem is inferred from finite state spaces

Every fixed finite graph gives a finite chain. Uniform estimates as the graph grows require additional proofs and should be stated separately.

## 10. Exercises

1. Define the two-coordinate generator directly on functions and prove its row-sum-zero property.
2. Show that independent component semigroups combine as a tensor product by proving the lifted generators commute.
3. Verify product stationarity and reversibility for n independent two-state chains.
4. Prove that the two-spin heat-bath generator is reversible with respect to its Gibbs distribution.
5. Give a neighbor-dependent rate for which the product of one-site stationary laws is not stationary.
6. Prove that coordinate updates at distinct sites commute as functions.
7. Identify which steps of the minimum spectral-gap proof use reversibility.
8. For a three-site path Ising model, write the local conditional law at the middle site and state its dependency neighborhood.
9. Explain why a sequential sweep of site-update kernels is not automatically the semigroup of the continuous-time generator sum.
10. State a finite-graph theorem whose constants are uniform in the graph size, and list the extra estimates it would require.

## Summary

Finite local systems can be represented as functions from sites to local states, with generators expressed as sums of coordinate-replacement increments. Independent component generators lift to commuting operators, which yield product semigroups, product stationary laws, and (in the reversible finite setting) a gap controlled by the slowest factor. Interactions preserve the local-update form but invalidate automatic factorization. The two-spin heat-bath chain shows how conditional probabilities give local rates and detailed balance with a Gibbs law. In Lean, coordinate-update lemmas, generator-action identities, and the boundary between observable and matrix representations are the key reusable interfaces.

## Further reading

- Chapter 50 for Gibbs sampling and conditional kernels.
- Chapters 55–60 for generators, semigroups, reversibility, and spectral gaps.
- [Mathlib’s matrix Kronecker product documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Kronecker.html).
- [Mathlib’s Markov-kernel composition documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html).

## 11. Lean formalization: independent and interacting coordinates

For two binary sites, flipping distinct coordinates commutes. The
corresponding constant-rate coordinate generators also commute on every
observable. To contrast this with interaction, let the first-site flip rate
depend on the current value at the second site. A concrete observable then
exhibits a nonzero commutator. The calculation isolates the algebraic reason
that product semigroups factor for independent coordinates but not for
general local interactions.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def updateFirst (p : State × State) : State × State :=
  (if p.1 = zero then one else zero, p.2)

theorem localUpdateLeavesSecondCoordinate : (updateFirst (zero, one)).2 = one := by decide
```

Now define both coordinate flips and their generator actions.

```lean
import Mathlib
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def updateSecond (p : State × State) : State × State :=
  (p.1, if p.2 = zero then one else zero)

def firstCoordinateGeneratorQ (r : ℚ) (f : State × State → ℚ)
    (p : State × State) : ℚ :=
  r * (f (updateFirst p) - f p)

def secondCoordinateGeneratorQ (s : ℚ) (f : State × State → ℚ)
    (p : State × State) : ℚ :=
  s * (f (updateSecond p) - f p)

theorem different_coordinate_updates_commute (p : State × State) :
    updateFirst (updateSecond p) = updateSecond (updateFirst p) := by
  cases p with
  | mk x y => rfl

theorem independent_coordinate_generators_commute (r s : ℚ)
    (f : State × State → ℚ) (p : State × State) :
    firstCoordinateGeneratorQ r (secondCoordinateGeneratorQ s f) p =
      secondCoordinateGeneratorQ s (firstCoordinateGeneratorQ r f) p := by
  simp only [firstCoordinateGeneratorQ, secondCoordinateGeneratorQ]
  rw [← different_coordinate_updates_commute p]
  ring

def interactingFirstGeneratorQ (f : State × State → ℚ)
    (p : State × State) : ℚ :=
  (if p.2 = zero then 1 else 2) * (f (updateFirst p) - f p)

def firstCoordinateIndicatorQ (p : State × State) : ℚ :=
  if p.1 = zero then 1 else 0

theorem local_interaction_breaks_generator_commutation :
    interactingFirstGeneratorQ
        (secondCoordinateGeneratorQ 1 firstCoordinateIndicatorQ) (zero, zero) ≠
      secondCoordinateGeneratorQ 1
        (interactingFirstGeneratorQ firstCoordinateIndicatorQ) (zero, zero) := by
  norm_num [interactingFirstGeneratorQ, secondCoordinateGeneratorQ,
    firstCoordinateIndicatorQ, updateFirst, updateSecond, zero, one]
```
