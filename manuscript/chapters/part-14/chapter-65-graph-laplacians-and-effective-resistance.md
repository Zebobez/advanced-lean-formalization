# Chapter 65 — Graph Laplacians and Effective Resistance

> **Audience.** This chapter assumes finite graph theory, linear algebra, reversible Markov chains, and the Dirichlet-form viewpoint from Chapter 60. It develops the network interpretation of those ideas and highlights a variational proof style that formalizes well.

Chapter 63 reduced a one-dimensional hitting problem to sums over path edges. The same ideas extend to any finite connected network. A reversible chain determines conductances on graph edges; harmonic functions are voltage profiles; and the Dirichlet form measures dissipated energy. Effective resistance then summarizes how easily the chain can move between two states. This chapter builds those connections while keeping normalization conventions explicit, especially for continuous-time commute times.

## Learning objectives

By the end of the chapter, you should be able to:

- define a weighted graph Laplacian and its Dirichlet energy;
- derive harmonicity from a reversible continuous-time generator;
- characterize voltage profiles as energy minimizers;
- compute effective resistance in paths and small parallel networks;
- state the continuous-time commute-time identity with its stationary-mass factor;
- organize variational and matrix proofs in Lean.

## 1. Finite conductance networks

Let V be a finite type and let (c:V\times V\to\mathbb R) assign conductances. Assume (c(x,y)=c(y,x)\geq0) and (c(x,x)=0). An edge is present exactly when (c(x,y)>0). Connectivity means that every pair of vertices is joined by a finite path of positive-conductance edges.

For a potential (f:V\to\mathbb R), define the weighted graph Laplacian
\[
  (\Delta_c f)(x)=\sum_{y\in V}c(x,y)(f(x)-f(y)).
\]
The associated energy is
\[
  \mathcal E_c(f,f)=\frac12\sum_{x,y\in V}
       c(x,y)(f(x)-f(y))^2
    =\sum_{\{x,y\}}c(x,y)(f(x)-f(y))^2,
\]
where the final sum ranges over unordered edges and counts each edge once. The factor one-half in the ordered-pair expression is necessary because symmetry counts every undirected edge twice.

The Laplacian annihilates constant functions. Its quadratic form is the energy:
\[
  \sum_x f(x)(\Delta_c f)(x)=\mathcal E_c(f,f).
\]
To see this, expand the left side, pair the term indexed by (x,y) with the one indexed by (y,x), and use symmetry of c. Every summand becomes half of a squared difference. Thus the Laplacian is positive semidefinite, and its kernel consists exactly of functions constant on each connected component. Connectivity reduces the kernel to the one-dimensional constant subspace.

## 2. Reversible generators as weighted Laplacians

Let Q be the generator of an irreducible finite continuous-time chain, with off-diagonal rates (q(x,y)\geq0), and let π be a strictly positive reversible stationary measure. Define
\[
  c(x,y)=\pi(x)q(x,y)=\pi(y)q(y,x).
\]
The conductances are symmetric and vanish on the diagonal. Since
\[
  (Qf)(x)=\sum_y q(x,y)(f(y)-f(x)),
\]
we have the pointwise relation
\[
  -\pi(x)(Qf)(x)=(\Delta_c f)(x).
\]
Consequently, the usual reversible Dirichlet form is exactly the network energy:
\[
  -\sum_x\pi(x)f(x)(Qf)(x)=\mathcal E_c(f,f).
\]

If π is a probability measure, its total mass is one; if π is left unnormalized, its mass is (M=\sum_x\pi(x)). The conductances scale linearly with π, so energies scale linearly and effective resistances scale inversely. State the normalization in theorem hypotheses. Silent normalization changes are a frequent source of missing factors in network identities.

One useful formalization is to define c from the pair `(π,Q)` rather than assume an unrelated weight function, then prove symmetry from detailed balance. For general weighted networks, define c directly. A theorem relating both settings can then transfer results without forcing graph-theoretic definitions to depend on a stochastic-process API.

## 3. Harmonic functions and boundary values

Choose disjoint nonempty boundary sets A and B. A potential f is harmonic away from the boundary if
\[
  (\Delta_c f)(x)=0\qquad(x\notin A\cup B).
\]
Equivalently, at each interior vertex, f(x) is the conductance-weighted average of its neighbors’ potentials. If the boundary values are one on A and zero on B, the harmonic function is the probability that the continuous-time chain hits A before B, provided it is stopped at the first boundary hit.

The generator equation and Laplacian equation differ by the positive factor π(x), so their interior zero sets agree. This identifies the stochastic hitting problem with a network boundary-value problem. On a finite connected graph, the solution is unique: if two solutions have the same boundary values, their difference is harmonic and zero on the boundary; the maximum principle forces the difference to vanish.

For a Lean proof, make the boundary set a `Finset V` or a predicate and state disjointness explicitly. Define the admissible potentials by their boundary values. The maximum-principle proof needs connectivity from each interior vertex to some boundary vertex; global connectedness and a nonempty boundary imply this, but the formal path argument should expose where it is used. The uniqueness theorem is purely finite and can be completed before introducing a Markov chain.

## 4. The Dirichlet principle

Among all potentials that equal one on A and zero on B, the harmonic potential uniquely minimizes energy. This is the Dirichlet principle. To prove it, let h be harmonic with the specified boundary values and write any other admissible potential as (f=h+g), where g vanishes on the boundary. By bilinearity,
\[
  \mathcal E_c(f,f)=\mathcal E_c(h,h)+2\mathcal E_c(h,g)+\mathcal E_c(g,g).
\]
The cross term vanishes. In the bilinear expansion of ℐ(h,g), group by vertices to obtain ∑_x g(x)(Δ_c h)(x). The factor g(x) is zero on the boundary and the Laplacian of h is zero in the interior. Hence
\[
  \mathcal E_c(f,f)=\mathcal E_c(h,h)+\mathcal E_c(g,g)
  \geq\mathcal E_c(h,h).
\]
If the network is connected and g is zero on the boundary, zero energy forces g to be constant and therefore zero, proving uniqueness of the minimizer.

This proof is better suited to formalization than differentiating an energy function and appealing to an optimization theorem. It uses a bilinear-form expansion, a finite-sum rearrangement, harmonicity, and nonnegativity. Each step has a reusable algebraic lemma. If using a generic quadratic-form API, first prove that its bilinear form matches the edge sum; otherwise the abstraction may hide the exact cancellation needed.

## 5. Effective conductance and resistance

For unit voltage difference between A and B, define the effective conductance by
\[
  C_{\mathrm{eff}}(A,B)=\min\{\mathcal E_c(f,f):
             f|_A=1,\ f|_B=0\}.
\]
The minimum is attained by the harmonic potential h. Define effective resistance as
\[
  R_{\mathrm{eff}}(A,B)=C_{\mathrm{eff}}(A,B)^{-1}.
\]
For disjoint nonempty boundary sets in a connected network, the effective conductance is positive: a zero-energy potential would be constant across every edge and could not take both boundary values. Thus the reciprocal is well-defined.

An equivalent description uses current. The current from x to y under potential h is (I(x,y)=c(x,y)(h(x)-h(y))). At an interior vertex, harmonicity says total outgoing current is zero. The total current leaving A equals the energy when the voltage difference is one, by summing potential times net current and canceling interior terms. Thus the minimum energy is precisely the current required for unit voltage, which is conductance.

In Lean, it is often simpler to define effective conductance as the energy of the unique harmonic solution than as an infimum. One then proves the Dirichlet principle and shows this value is the minimum. A `sInf` or `IsGreatest` characterization remains useful for general variational theorems, but can introduce order-completeness obligations that obscure the finite-dimensional argument.

## 6. Worked example: parallel routes in a triangle

Take three vertices A, B, C. Join A to B by a unit-conductance edge; also join A to C and C to B by unit-conductance edges. Set potential one at A and zero at B. By symmetry, the harmonic potential at C is one-half: the two incident currents cancel. The direct edge carries current one. The two-edge route carries current one-half, since each edge has a potential drop of one-half. Total current is (3/2), so effective conductance is (3/2) and resistance is (2/3).

The same result follows from series and parallel rules. The two edges through C have resistance one each, so their series resistance is 2. This route is in parallel with a direct resistance-one edge, giving
\[
  R_{\mathrm{eff}}^{-1}=1^{-1}+2^{-1}=\frac32.
\]
The variational calculation and circuit reduction are two presentations of the same finite sum identities. An exercise is to formalize the harmonic equations as a three-variable linear system and derive the minimum energy without using a circuit simplification theorem.

For comparison, on a path with edge conductances c_0,...,c_{N-1}, a unit current must pass through every edge. The voltage drop across edge k is (1/c_k), so the total voltage drop and resistance are
\[
  R_{\mathrm{eff}}(0,N)=\sum_{k=0}^{N-1}\frac1{c_k}.
\]
This recovers the resistance sum from Chapter 63. In a general graph, multiple routes split the current, which is why the full harmonic problem is needed.

## 7. Continuous-time commute times and normalization

For an irreducible reversible continuous-time chain on finite V, let (T_b) be the first hitting time of b and use conductances (c(x,y)=\pi(x)q(x,y)), where π may be any positive stationary measure satisfying detailed balance. Then
\[
  \mathbb E_a[T_b]+\mathbb E_b[T_a]
    =\Bigl(\sum_{x\in V}\pi(x)\Bigr)R_{\mathrm{eff}}(a,b).
\]
If π is normalized to a probability, the prefactor is one. This form is specific to the continuous-time generator and its conductance convention. The factor would look different if one instead used unnormalized edge conductances for an embedded discrete-time random walk.

The formula links expected travel time to network resistance and total stationary mass. Its normalization can be checked on a two-state chain with rates a from 0 to 1 and b from 1 to 0. Take π(0)=b and π(1)=a. There is one edge of conductance ab, so resistance is (1/(ab)). The stationary mass is a+b. The right side is ((a+b)/(ab)=1/a+1/b), exactly the sum of the two exponential mean holding times.

The theorem can be derived from the Poisson equations for expected hitting times. First solve a unit-current potential problem; then pair the hitting-time equations with that potential using reversibility and finite-sum summation by parts. In a formal proof, isolate this summation-by-parts identity and keep π’s total mass explicit until the final line. Avoid inserting `IsProbabilityMeasure π` too early if unnormalized measures make the algebra clearer.

## 8. Matrix Laplacians and Mathlib

For an unweighted finite simple graph, Mathlib defines the Laplacian matrix as the degree matrix minus the adjacency matrix. Its API proves positive semidefiniteness and relates the nullspace dimension to connected components. This is a valuable starting point for formal graph arguments and can replace hand-built matrices in unweighted examples.

The weighted operator used in this chapter is more general than that simple-graph Laplacian. A weighted adjacency matrix has entries c(x,y), a weighted degree is ∑_y c(x,y), and their difference acts by the formula Δ_c above. One can define that matrix directly and prove the quadratic-form energy identity. Do not silently apply the unweighted theorem to a weighted model; either restrict to unit weights or prove the weighted analogue.

There are two complementary formal routes. For matrix spectral results, encode the weighted Laplacian as a symmetric matrix and use finite-dimensional self-adjoint linear algebra. For hitting and minimization arguments, use functions and finite sums. These routes can be connected by a theorem identifying matrix-vector action with the function-level Laplacian. The function-level statement should usually be the user-facing theorem because it does not expose a particular vertex enumeration.

## 9. Proof architecture and reusable lemmas

Separate a network development into these interfaces:

1. **Conductance assumptions:** symmetry, nonnegativity, zero diagonal, and finite support or finiteness of V.
2. **Quadratic energy:** an edge-sum definition and its nonnegativity.
3. **Summation by parts:** the identity between energy pairing and Laplacian action.
4. **Connectivity consequences:** zero energy implies componentwise constancy.
5. **Boundary solver:** existence and uniqueness of a harmonic potential.
6. **Variational theorem:** harmonicity makes the potential minimize energy.
7. **Stochastic bridge:** detailed balance identifies the graph operator with −πQ.

The dependency flow is:

```text
conductances ──> Laplacian and edge energy ──> harmonic boundary solver
                         │                              │
                         v                              v
                  summation by parts ─────────> Dirichlet principle
                         │                              │
          reversible generator                    effective resistance
                                                        │
                                                        v
                                                commute-time identity
```

This order prevents a common proof-design failure: mixing matrix indices, graph connectivity, and stopping-time integrability in one theorem. The finite network algebra should be established first. The stochastic theorem then becomes a concise application of the generator and Poisson-equation results from earlier chapters.

## 10. Common failure modes

### Each undirected edge is counted twice

The ordered-pair formula uses one-half; the unordered-edge formula does not. Prove the conversion explicitly.

### The constant mode is mistaken for strict positivity

The Laplacian is positive semidefinite, not positive definite on all functions. Restrict to functions vanishing on a nonempty boundary or to mean-zero functions.

### Connectivity is omitted from uniqueness

Disconnected components can carry different constants. State the connectivity condition that reaches the boundary.

### Resistance is inverted with the wrong convention

Unit-voltage minimum energy is effective conductance. Effective resistance is its reciprocal.

### Stationary mass is silently normalized

Rescaling π rescales conductances and inversely rescales resistance. Keep ∑π explicit in commute-time identities.

### An unweighted graph theorem is applied to weighted rates

Mathlib’s simple-graph Laplacian uses adjacency and degree. Weighted generators require a weighted operator or a reduction with justified weights.

## 11. Representing edges and proving finite minima

The ordered-pair energy formula is often the easiest Lean definition:
\[
  \mathcal E_c(f,f)=\frac12\sum_{x\in V}\sum_{y\in V}
  c(x,y)(f(x)-f(y))^2.
\]
It needs only finite sums, symmetry, and real arithmetic. The unordered-edge version reads more like a circuit model, but requires choosing an edge type or quotienting pairs by reversal. A simple graph’s edges can be represented by `Sym2 V`; weighted networks can attach a conductance to each unordered edge, or retain a symmetric pair function and use the factor one-half. Avoid a hand-picked orientation unless later theorems genuinely need directed edges.

The variational definition also has a finite-dimensional existence proof. The admissible potentials form a nonempty affine subspace of (V\to\mathbb R), and the energy is a positive-semidefinite quadratic form. With boundary values fixed on both sides and a connected network, the energy is coercive on the free coordinates: zero energy for a boundary-zero difference forces that difference to vanish. One may therefore use finite-dimensional compactness after restricting to a bounded sublevel set, or sidestep the general existence theorem by solving the finite harmonic linear system and proving the Dirichlet principle. The second route usually gives cleaner proof states and a more constructive witness for the minimizer.

For a small graph, computation can still be useful. Enumerate its vertices, build the weighted Laplacian matrix, and let `norm_num` or `ring` verify the proposed voltage and energy identities. Treat this as a checked example, not the general theorem: the abstract proof should quantify over V and conductances and use the same edge-energy identity for every finite network.

## 12. Exercises

1. Prove the energy identity by pairing ordered terms (x,y) and (y,x).
2. Show that zero energy implies constancy on each connected component.
3. Prove uniqueness of a harmonic potential with fixed boundary values.
4. Establish the Dirichlet principle by expanding (f=h+g).
5. Compute effective resistance between opposite vertices of a square with unit edge conductances.
6. Derive the path resistance formula by solving the constant-current equations.
7. Verify the two-state continuous-time commute-time identity for arbitrary positive rates.
8. State and prove the conversion from a reversible generator to a weighted Laplacian.
9. Explain why a potential that minimizes energy is harmonic at every interior vertex.
10. Design a Lean structure for a finite conductance network that supports both a graph-theoretic and a stochastic interpretation.

## Summary

A finite reversible chain defines a symmetric conductance network. Its generator equation becomes a weighted graph Laplacian equation, and its Dirichlet form becomes electrical energy. Harmonic potentials uniquely solve boundary hitting problems and minimize energy; effective resistance is the reciprocal of the minimum energy under unit voltage. Paths recover the resistance sums from Chapter 63, while parallel routes illustrate how general graphs distribute current. For continuous-time chains, the commute time equals effective resistance times total stationary mass under (c(x,y)=\pi(x)q(x,y)). Formal proofs are clearest when the network algebra, variational argument, and probabilistic interpretation are separate interfaces.

## Further reading

- Chapters 48, 60, and 63 for total variation, reversible Dirichlet forms, spectral gaps, and path networks.
- [Mathlib’s finite simple-graph Laplacian documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/LapMatrix.html).
- [Mathlib’s graph incidence-matrix documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/IncMatrix.html).

## 13. Lean formalization: the three-vertex path

Consider a path with vertices `0`, `1`, and `2`, and positive conductances
`c₀` and `c₁` on its two edges. The harmonic voltage with boundary values
one at zero and zero at two is `c₀ / (c₀ + c₁)` at the middle vertex. Its
energy is `c₀c₁ / (c₀ + c₁)`, so the effective resistance is the series sum
`1/c₀ + 1/c₁`. The formalization proves the Laplacian–energy identity and
an exact completion-of-the-square formula; the latter establishes the
Dirichlet minimum for every potential with the same boundary values.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def neighbor (s : State) : State := if s = zero then one else zero
def contrastPotential : State → Int := fun s => if s = zero then 1 else -1
def graphLaplacian (s : State) : Int := contrastPotential s - contrastPotential (neighbor s)

theorem laplacianAtZero : graphLaplacian zero = 2 := by decide
theorem laplacianAtOne : graphLaplacian one = -2 := by decide
```

The rational path definitions use one term for each incident edge.

```lean
import Mathlib

def pathLaplacianQ (c₀ c₁ : ℚ) (f : Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  if i = 0 then c₀ * (f 0 - f 1)
  else if i = 1 then
    c₀ * (f 1 - f 0) + c₁ * (f 1 - f 2)
  else c₁ * (f 2 - f 1)

def pathEnergyQ (c₀ c₁ : ℚ) (f : Fin 3 → ℚ) : ℚ :=
  c₀ * (f 0 - f 1) ^ 2 + c₁ * (f 1 - f 2) ^ 2

def pathLaplacianPairingQ (c₀ c₁ : ℚ) (f : Fin 3 → ℚ) : ℚ :=
  f 0 * pathLaplacianQ c₀ c₁ f 0 +
    f 1 * pathLaplacianQ c₀ c₁ f 1 +
    f 2 * pathLaplacianQ c₀ c₁ f 2

def pathVoltageQ (c₀ c₁ : ℚ) (i : Fin 3) : ℚ :=
  if i = 0 then 1 else if i = 1 then c₀ / (c₀ + c₁) else 0

theorem path_energy_eq_laplacian_pairing (c₀ c₁ : ℚ) (f : Fin 3 → ℚ) :
    pathEnergyQ c₀ c₁ f = pathLaplacianPairingQ c₀ c₁ f := by
  simp [pathEnergyQ, pathLaplacianPairingQ, pathLaplacianQ]
  ring

theorem path_voltage_boundary_values (c₀ c₁ : ℚ) :
    pathVoltageQ c₀ c₁ 0 = 1 ∧ pathVoltageQ c₀ c₁ 2 = 0 := by
  simp [pathVoltageQ]

theorem path_voltage_is_harmonic (c₀ c₁ : ℚ)
    (h : c₀ + c₁ ≠ 0) :
    pathLaplacianQ c₀ c₁ (pathVoltageQ c₀ c₁) 1 = 0 := by
  simp [pathLaplacianQ, pathVoltageQ]
  field_simp [h]
  ring

theorem path_voltage_energy (c₀ c₁ : ℚ) (h : c₀ + c₁ ≠ 0) :
    pathEnergyQ c₀ c₁ (pathVoltageQ c₀ c₁) = c₀ * c₁ / (c₀ + c₁) := by
  simp [pathEnergyQ, pathVoltageQ]
  field_simp [h]
  ring

theorem path_energy_completion_of_square (c₀ c₁ : ℚ)
    (h : c₀ + c₁ ≠ 0) (f : Fin 3 → ℚ)
    (h₀ : f 0 = 1) (h₂ : f 2 = 0) :
    pathEnergyQ c₀ c₁ f =
      pathEnergyQ c₀ c₁ (pathVoltageQ c₀ c₁) +
        (c₀ + c₁) * (f 1 - c₀ / (c₀ + c₁)) ^ 2 := by
  simp only [pathEnergyQ]
  rw [h₀, h₂]
  simp [pathVoltageQ]
  field_simp [h]
  ring

theorem path_voltage_minimizes_energy (c₀ c₁ : ℚ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (f : Fin 3 → ℚ)
    (h : c₀ + c₁ ≠ 0) (h₀ : f 0 = 1) (h₂ : f 2 = 0) :
    pathEnergyQ c₀ c₁ (pathVoltageQ c₀ c₁) ≤ pathEnergyQ c₀ c₁ f := by
  rw [path_energy_completion_of_square c₀ c₁ h f h₀ h₂]
  have hsum : 0 ≤ c₀ + c₁ := by linarith
  have hsq : 0 ≤ (f 1 - c₀ / (c₀ + c₁)) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hsum hsq]

theorem path_effective_conductance_times_resistance (c₀ c₁ : ℚ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    (c₀ * c₁ / (c₀ + c₁)) * ((c₀ + c₁) / (c₀ * c₁)) = 1 := by
  have hsum : c₀ + c₁ ≠ 0 := ne_of_gt (by linarith)
  have hprod : c₀ * c₁ ≠ 0 := mul_ne_zero (ne_of_gt hc₀) (ne_of_gt hc₁)
  field_simp [hsum, hprod]

theorem path_effective_resistance_is_series_sum (c₀ c₁ : ℚ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    (c₀ + c₁) / (c₀ * c₁) = 1 / c₀ + 1 / c₁ := by
  have hprod : c₀ * c₁ ≠ 0 := mul_ne_zero (ne_of_gt hc₀) (ne_of_gt hc₁)
  field_simp [ne_of_gt hc₀, ne_of_gt hc₁, hprod]
  ring
```
