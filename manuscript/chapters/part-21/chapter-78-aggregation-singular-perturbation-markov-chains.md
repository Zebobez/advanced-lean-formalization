# Chapter 78 — Aggregation and Singular Perturbation of Markov Chains

> **Audience.** This chapter assumes finite-state continuous-time chains, invariant distributions, generators, and the fast–slow framework of Chapter 77. It reduces a large chain with rapidly mixing state classes to a smaller chain on those classes.

A finite Markov chain may contain groups of states that communicate rapidly inside each group but only rarely between groups. On the time scale of the between-group motion, the chain spends most of its time near the stationary distribution of its current group. The effective transition rate between groups is therefore the within-group stationary average of the original slow rates.

This reduction is called aggregation or singular perturbation. It is different from exact lumpability: an exactly lumpable partition produces a Markov chain on blocks at every parameter value, while singular perturbation produces a Markov approximation only in the fast-mixing limit. The proof can be organized through a projection onto block-constant functions and a Poisson corrector within each block.

## Learning objectives

By the end of the chapter, you should be able to:

- represent a nearly decomposable generator as a fast part plus a slow perturbation;
- derive the effective generator on communicating classes;
- construct a perturbed test function using blockwise Poisson equations;
- distinguish asymptotic aggregation from exact lumpability;
- relate the limiting stationary law to fast within-class equilibria;
- formalize the projection, corrector, and martingale-problem steps.

## 1. Fast blocks and a perturbed generator

Let S be a finite state space partitioned into disjoint nonempty blocks \(C_1,\ldots,C_m\). Write \(c(i)=a\) when state i belongs to block \(C_a\). Consider a family of generators
\[
  Q^\varepsilon=\frac1\varepsilon Q_0+Q_1,
  \qquad \varepsilon>0.
\]
Assume \(Q_0\) is block diagonal and its restriction \(Q_0^a\) to each \(C_a\) is irreducible. The generator \(Q_1\) represents slow transitions and is itself a generator on S. Then \(Q^\varepsilon\) is a generator, and within-block motion is accelerated by \(1/\varepsilon\).

For each block, let \(\pi^a\) be the stationary distribution of \(Q_0^a\). A function \(f:S\to\mathbb R\) is block-constant if \(f(i)\) depends only on \(c(i)\). Such functions lie in the kernel of \(Q_0\). They describe observables that do not see the fast state inside a block.

The limiting process records only \(c(X^\varepsilon_t)\). Its state space is the smaller set \(\{1,\ldots,m\}\). The main question is to calculate its transition rates and prove that the aggregated trajectory converges to a Markov chain with those rates.

## 2. Deriving the averaged generator

For blocks a and b with \(a\ne b\), define
\[
  \bar q(a,b)=\sum_{i\in C_a}\pi^a(i)
                   \sum_{j\in C_b}q_1(i,j).
\]
The slow rate out of a block depends on the current fast state i. Fast equilibration replaces i by a draw from \(\pi^a\), so the effective rate is the stationary average of all rates crossing from \(C_a\) to \(C_b\). Set
\[
  \bar q(a,a)=-\sum_{b\ne a}\bar q(a,b).
\]
Off-diagonal entries are nonnegative and rows sum to zero, so \(\bar Q=(\bar q(a,b))\) is a generator on the block space.

Equivalently, for a block function \(\varphi\) define its lift \(\widetilde\varphi(i)=\varphi(c(i))\). Then
\[
  (\bar Q\varphi)(a)=\sum_{i\in C_a}\pi^a(i)
                      (Q_1\widetilde\varphi)(i).
\]
This form includes the diagonal contribution and often gives a cleaner proof than summing only cross-block rates. It says: apply the slow generator to a block observable, then average the result under the fast equilibrium in that block.

## 3. Perturbed test functions

The lifted function \(\widetilde\varphi\) is annihilated by \(Q_0\), but \(Q_1\widetilde\varphi\) need not be block-constant. To control its within-block variation, define the centered residual
\[
  r_\varphi(i)=(Q_1\widetilde\varphi)(i)
                  -(\bar Q\varphi)(c(i)).
\]
By construction, \(\sum_{i\in C_a}\pi^a(i)r_\varphi(i)=0\) for every block a. Therefore the blockwise Poisson equation
\[
  Q_0\chi_\varphi=-r_\varphi,
  \qquad \sum_{i\in C_a}\pi^a(i)\chi_\varphi(i)=0
\]
has a unique solution on each block.

Use the corrected test function
\[
  \varphi^\varepsilon=\widetilde\varphi+\varepsilon\chi_\varphi.
\]
Its generator is
\[
  Q^\varepsilon\varphi^\varepsilon
   =Q_0\chi_\varphi+Q_1\widetilde\varphi
       +\varepsilon Q_1\chi_\varphi
   =\widetilde{\bar Q\varphi}+\varepsilon Q_1\chi_\varphi.
\]
Since S is finite, \(\chi_\varphi\) is bounded, so the correction to the test function vanishes uniformly as ε tends to zero. The remaining generator error is order \(\varepsilon\). This is the key calculation behind convergence of the martingale problems.

The sign in the Poisson equation is chosen so that \(Q_0\chi+Q_1\widetilde\varphi\) equals the averaged generator. It is worth checking this cancellation explicitly: an opposite sign doubles the centered residual instead of removing it.

### Projection onto block observables

Define a projection on state functions by
\[
  (\Pi f)(i)=\sum_{j\in C_{c(i)}}\pi^{c(i)}(j)f(j).
\]
Its image is the block-constant subspace, and \(\Pi^2=\Pi\). Invariance of each \(\pi^a\) gives \(\Pi Q_0=0\), while block constancy gives \(Q_0\Pi=0\). The reduced generator is the restriction of \(\Pi Q_1\) to block-constant functions. The corrector solves
\[
  Q_0\chi=-(I-\Pi)Q_1\widetilde\varphi,
  \qquad \Pi\chi=0.
\]
This compact form packages all blockwise equations into one projection equation. In a formal proof, the kernel-range decomposition is explicit: \(\ker Q_0=\operatorname{range}\Pi\), while \(\operatorname{range}Q_0=\ker\Pi\). The normalized inverse is then a linear equivalence between the centered subspace and itself.

The projection formulation also clarifies the relationship to adiabatic elimination in linear algebra. The slow operator is not simply \(Q_1\) restricted to the kernel; it is first projected back to that kernel after applying \(Q_1\). The corrector records the component that leaves the kernel and is canceled by fast relaxation.

## 4. Convergence of the aggregated process

Suppose the initial block \(c(X^\varepsilon_0)\) has a limiting distribution and the initial fast state is arbitrary. The fast chain relaxes within its starting block over a time of order \(\varepsilon\). A slow transition during this initial layer has probability of order \(\varepsilon\) on a fixed horizon, so the initial fast state does not affect the limiting block process.

The corrected test function gives a martingale
\[
  M_t^\varepsilon=\varphi^\varepsilon(X_t^\varepsilon)
       -\varphi^\varepsilon(X_0^\varepsilon)
       -\int_0^tQ^\varepsilon\varphi^\varepsilon(X_s^\varepsilon)\,ds.
\]
The generator identity shows that, up to a uniformly vanishing corrector and an order-ε integrated remainder, the block observable evolves with generator \(\bar Q\). Tightness follows because transitions between blocks occur only through \(Q_1\), whose rates are bounded on finite S. Any subsequential limit solves the martingale problem for \(\bar Q\); uniqueness of the finite-state chain with generator \(\bar Q\) identifies the full limit.

This argument establishes weak convergence of the aggregate paths on fixed time intervals. It does not claim that the original state path converges to a path on the block space without applying c, nor that the two chains can be coupled to agree at every time. The fast coordinate continues to move rapidly inside each block even as the aggregate process has a well-defined limit.

The tightness estimate is simple but important. The number of blocks is finite, and the total rate of cross-block moves is bounded by the maximum exit rate of \(Q_1\), independently of ε. Thus the aggregate paths cannot make arbitrarily many jumps on a bounded interval with substantial probability. Rapid \(Q_0\)-motion does not appear in this rate because it leaves c(X) unchanged.

## 5. Worked example: two fast classes

Take four states partitioned into \(C_A=\{a_0,a_1\}\) and \(C_B=\{b_0,b_1\}\). Within A, the fast rates are \(a_0\to a_1\) at p and \(a_1\to a_0\) at q. Within B, they are \(b_0\to b_1\) at r and \(b_1\to b_0\) at s. All four rates are positive. The fast stationary weights are
\[
  \pi^A(a_0)=\frac q{p+q},\quad \pi^A(a_1)=\frac p{p+q},
  \qquad
  \pi^B(b_0)=\frac s{r+s},\quad \pi^B(b_1)=\frac r{r+s}.
\]
Let the slow cross-block rates be \(a_0\to b_0\) at u, \(a_1\to b_1\) at v, \(b_0\to a_0\) at w, and \(b_1\to a_1\) at z. The reduced rates are
\[
  \bar q(A,B)=\frac{qu+pv}{p+q},\qquad
  \bar q(B,A)=\frac{sw+rz}{r+s}.
\]
The stationary probability of block B in the reduced two-state chain is
\[
  \bar\pi(B)=\frac{\bar q(A,B)}
                       {\bar q(A,B)+\bar q(B,A)}.
\]
Notice that this is not generally the stationary probability obtained by simply summing the stationary law of the full four-state chain at a fixed ε. The equality holds only in the limit as ε tends to zero, and the fast weights within each block are essential to the average.

## 6. Exact lumpability versus asymptotic aggregation

A partition is exactly lumpable for a generator Q if, for every pair of blocks a,b, the total rate from \(i\in C_a\) to \(C_b\) is independent of the choice of \(i\) in \(C_a\). Under this condition, \(c(X_t)\) is itself a Markov chain for every initial distribution, with generator given by those common cross-block rates. No separation of time scales is needed.

In the perturbation model, the rates from i∈C_a to C_b may differ. The aggregate need not be Markov at finite ε because its future depends on the unobserved fast state. But that state rapidly approaches \(\pi^a\), so the averaged rate becomes asymptotically valid. Exact lumpability is an algebraic identity; singular perturbation is a limiting theorem with mixing and tightness hypotheses.

The distinction affects formal proof structure. For exact lumpability, prove equality of block exit rates and use the Markov property directly. For asymptotic aggregation, construct the corrector and prove convergence of generators or martingale problems. Do not use an exact quotient theorem when the model only satisfies approximate rate equality.

### Worked example: an exact two-block quotient

Suppose every state in \(C_A\) has total rate \(\lambda\) to \(C_B\), and every state in \(C_B\) has total rate \(\mu\) to \(C_A\), even though the destination microstate may depend on the source. Internal transitions can have arbitrary rates. For a block function \(\varphi\), the value \((Q\varphi)(i)=\lambda(\varphi(B)-\varphi(A))\) on \(C_A\) is independent of i; on \(C_B\), it equals \(\mu(\varphi(A)-\varphi(B))\). The aggregate therefore has generator
\[
  \begin{pmatrix}-\lambda&\lambda\\\mu&-\mu\end{pmatrix}
\]
for every ε, not just in the limit. This is the defining rate identity for exact lumpability. In the singularly perturbed case, the same two blocks can have source-dependent exit rates; then the quotient is valid only after averaging them against \(\pi^A\) and \(\pi^B\).

## 7. Stationary distributions in the limit

Suppose \(Q^\varepsilon\) is irreducible for every ε and let \(\pi^\varepsilon\) be its stationary distribution. If the reduced generator \(\bar Q\) is also irreducible, then its stationary law \(\bar\pi\) determines the limit:
\[
  \pi^\varepsilon(i)\longrightarrow
       \bar\pi(a)\pi^a(i),\qquad i\in C_a.
\]
The leading-order stationary equation makes \(\pi^0\) stationary for \(Q_0\), so its restriction within each block must be a scalar multiple of \(\pi^a\). The next-order solvability condition averages \(Q_1\) across blocks and gives \(\bar\pi\bar Q=0\). This explains the product form of the limiting stationary mass.

If \(\bar Q\) is reducible, the stationary law of the limit is not unique. Then the leading-order equations alone may not determine how mass is split among closed aggregate classes. Higher-order perturbation terms or the initial distribution can select the limit. A proof should not divide by a supposedly unique stationary vector until irreducibility of the reduced generator has been established.

The next stationary correction is governed by a second Poisson equation. Formally write \(\pi^\varepsilon=\pi_0+\varepsilon\eta+o(\varepsilon)\). Substitution into \(\pi^\varepsilon Q^\varepsilon=0\) first gives \(\pi_0Q_0=0\), then
\[
  \eta Q_0=-\pi_0Q_1.
\]
This equation is solvable only when the right side has zero mass on every fast class. Those classwise solvability conditions are exactly the reduced stationary equation \(\bar\pi\bar Q=0\). After choosing the block masses, the remaining centered part of η is obtained by inverting \(Q_0\) on the complementary subspace. This is the row-vector counterpart of the function-valued corrector used for path convergence.

## 8. First-order corrections and error estimates

The corrected test function yields more than the limiting generator. For a fixed block observable, the residual in its generator equation is \(\varepsilon Q_1\chi_\varphi\). On finite S this is uniformly bounded by a constant times ε. Integrating over a fixed time horizon produces an order-ε weak error for expectations of smooth test observables, subject to uniform control of the initial corrector and the martingale problem.

The corrector also describes the leading conditional bias from the current fast state. Before the fast state equilibrates, the difference between \(Q_1\widetilde\varphi(i)\) and its block average is canceled by \(Q_0\chi(i)\). This provides a practical diagnostic: states with large \(|\chi(i)|\) create larger short-time aggregation errors, even when the limiting block generator is unchanged.

These estimates are not automatically total-variation bounds between path laws. Weak generator estimates control expectations in a test-function class; stronger metrics require quantitative mixing, coupling, or smoothing estimates. State the mode of convergence precisely in both mathematical statements and Lean theorem names.

## 9. Formalization architecture

Represent the partition by a surjective map \(c:S\to B\) with finite fibers, or by an equivalence between S and a sigma type of blocks and within-block states. Then define the fast and slow generators and prove:

1. \(Q_0\) preserves each block and has zero row sums;
2. each restricted fast generator has a normalized invariant law;
3. the averaged generator \(\bar Q\) has nonnegative off-diagonal entries and zero row sums;
4. blockwise centered residuals lie in the range of \(Q_0\);
5. normalized Poisson correctors exist uniquely;
6. corrected test functions have generator \(\widetilde{\bar Q\varphi}+O(\varepsilon)\);
7. tightness and uniqueness identify the limiting martingale problem.

The proof flow is:

```text
partition of S ──> block fast generators ──> invariant laws πᵃ
       │                                           │
       v                                           v
 lift block tests φ̃ ──> centered residual ──> Poisson corrector χ
                                                   │
                                                   v
                           corrected generator ──> reduced chain Q̄
```

Keep the finite-dimensional matrix result separate from the path convergence theorem. The first layer constructs \(\bar Q\) and χ using sums over finite types; the second uses sample paths, tightness, and uniqueness of a martingale problem. This makes the algebra reusable for stationary perturbation calculations even before a path-space convergence API is available.

## 10. Common failure modes

### The fast generator is not block diagonal

The kernel of \(Q_0\) must contain all block-constant functions. If \(Q_0\) moves between proposed blocks, the partition does not represent its recurrent classes and the projection is wrong.

### The residual is not centered in each block

The Poisson equation is solved separately on each fast class. Global centering across S is insufficient; verify zero mean under every \(\pi^a\).

### The slow generator is not a generator

For \(Q^\varepsilon=Q_0/\varepsilon+Q_1\) to preserve nonnegative off-diagonal rates at every \(\varepsilon\), require both components to have valid generator structure, or state a sufficiently small ε range and prove positivity there.

### A fast initial state is treated as stationary

The initial state may be arbitrary. Use the corrector to bound the initial layer rather than silently assuming equilibrium at time zero.

### Asymptotic aggregation is called exact lumpability

At finite ε the block process may not be Markov. Use the perturbed-generator argument and name the convergence mode.

### Stationary limits are inferred from path limits alone

Long-time and ε limits need not commute. Uniform tightness or stationary perturbation equations are needed for invariant-distribution convergence.

## 11. Exercises

1. Prove that the averaged off-diagonal rates are nonnegative and the reduced rows sum to zero.
2. Derive \(\bar Q\varphi(a)=\sum_i\pi^a(i)(Q_1\widetilde\varphi)(i)\).
3. Show that the blockwise Poisson residual is centered.
4. Verify the cancellation in the corrected generator and determine the required sign of \(Q_0\chi\).
5. Compute the two-block example’s stationary distribution and compare it with the fast-class weights.
6. State the exact lumpability criterion and prove that it makes the aggregate Markov at every \(\varepsilon\).
7. Derive the leading stationary distribution from the first two orders of \(\pi^\varepsilon Q^\varepsilon=0\).
8. Give an example where the reduced generator is reducible even though every perturbed generator is irreducible.
9. Explain why a weak generator error does not by itself imply a total-variation path bound.
10. Design a Lean structure for a partition, fast generators, invariant class laws, and the normalized corrector.

## Summary

For a generator \(Q^\varepsilon=Q_0/\varepsilon+Q_1\), fast irreducible classes of \(Q_0\) collapse into aggregate states. The effective rate between classes is the \(Q_1\) rate averaged against the stationary law within the starting class. A blockwise Poisson corrector makes the lifted generator converge to this reduced generator. Exact lumpability is stronger and holds at every scale; asymptotic aggregation requires fast mixing, corrector solvability, and a path convergence argument.

## Further reading

- Chapter 77 for averaging a fast environment that depends on a continuous slow state.
- G. Yin, H. Zhang, and G. Badowski, “Singularly Perturbed Markov Chains: Convergence and Aggregation,” *Journal of Multivariate Analysis* 72 (2000), 208–229, [doi:10.1006/jmva.1999.1855](https://doi.org/10.1006/jmva.1999.1855).
- G. Yin and H. Zhang, “Two-Time-Scale Markov Chains and Applications to Quasi-Birth-Death Queues,” *SIAM Journal on Applied Mathematics* 65 (2005), 567–586, [doi:10.1137/S003613990139756X](https://doi.org/10.1137/S003613990139756X).

## 12. Lean formalization: a two-block averaged generator

We formalize the four-state example from Section 5. Each fast block has two states; its invariant law weights a state by the incoming rate. Averaging the slow cross-block rates gives the reduced transition rates `(q u + p v)/(p+q)` and `(s w + r z)/(r+s)`. We also verify that the residual cross-block drift is centered in each fast block and that rate equality within each block recovers exact lumpability.

The original aggregation-label calculation is retained.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def aggregateToOneClass (_s : State) : Nat := 0

theorem aggregationErasesTheWithinClassLabel :
    aggregateToOneClass zero = aggregateToOneClass one := by decide
```

All rates below are rational and assumed positive when they occur in a denominator. `p,q` govern the fast motion in block A, `r,s` in block B, and `u,v,w,z` are the slow transitions crossing between those blocks.

```lean
def blockAWeightZero (p q : ℚ) : ℚ := q / (p + q)
def blockAWeightOne (p q : ℚ) : ℚ := p / (p + q)
def blockBWeightZero (r s : ℚ) : ℚ := s / (r + s)
def blockBWeightOne (r s : ℚ) : ℚ := r / (r + s)

def averagedRateAB (p q u v : ℚ) : ℚ :=
  blockAWeightZero p q * u + blockAWeightOne p q * v

def averagedRateBA (r s w z : ℚ) : ℚ :=
  blockBWeightZero r s * w + blockBWeightOne r s * z

theorem blockA_weights_normalized (p q : ℚ) (hp : 0 < p) (hq : 0 < q) :
    blockAWeightZero p q + blockAWeightOne p q = 1 := by
  have hs : p + q ≠ 0 := ne_of_gt (add_pos hp hq)
  unfold blockAWeightZero blockAWeightOne
  field_simp [hs]
  ring

theorem blockB_weights_normalized (r s : ℚ) (hr : 0 < r) (hs : 0 < s) :
    blockBWeightZero r s + blockBWeightOne r s = 1 := by
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold blockBWeightZero blockBWeightOne
  field_simp [hrs]
  ring

theorem residualA_centered (p q u v : ℚ) (hp : 0 < p) (hq : 0 < q) :
    blockAWeightZero p q * (u - averagedRateAB p q u v) +
      blockAWeightOne p q * (v - averagedRateAB p q u v) = 0 := by
  have hs : p + q ≠ 0 := ne_of_gt (add_pos hp hq)
  unfold averagedRateAB blockAWeightZero blockAWeightOne
  field_simp [hs]
  ring

theorem residualB_centered (r s w z : ℚ) (hr : 0 < r) (hs : 0 < s) :
    blockBWeightZero r s * (w - averagedRateBA r s w z) +
      blockBWeightOne r s * (z - averagedRateBA r s w z) = 0 := by
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold averagedRateBA blockBWeightZero blockBWeightOne
  field_simp [hrs]
  ring

theorem averagedRateAB_exact_lumpability (p q u : ℚ) (hp : 0 < p) (hq : 0 < q) :
    averagedRateAB p q u u = u := by
  have hs : p + q ≠ 0 := ne_of_gt (add_pos hp hq)
  unfold averagedRateAB blockAWeightZero blockAWeightOne
  field_simp [hs]
  ring

theorem averagedRateBA_exact_lumpability (r s w : ℚ)
    (hr : 0 < r) (hs : 0 < s) : averagedRateBA r s w w = w := by
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold averagedRateBA blockBWeightZero blockBWeightOne
  field_simp [hrs]
  ring

inductive ReducedBlock where
  | A
  | B
  deriving DecidableEq

def reducedGenerator (p q r s u v w z : ℚ) :
    ReducedBlock → ReducedBlock → ℚ
  | .A, .A => -averagedRateAB p q u v
  | .A, .B => averagedRateAB p q u v
  | .B, .A => averagedRateBA r s w z
  | .B, .B => -averagedRateBA r s w z

theorem reducedGenerator_rowA_sum (p q r s u v w z : ℚ) :
    reducedGenerator p q r s u v w z .A .A +
      reducedGenerator p q r s u v w z .A .B = 0 := by
  simp [reducedGenerator]

theorem reducedGenerator_rowB_sum (p q r s u v w z : ℚ) :
    reducedGenerator p q r s u v w z .B .A +
      reducedGenerator p q r s u v w z .B .B = 0 := by
  simp [reducedGenerator]
```

The averaged off-diagonal rates are nonnegative combinations of the original rates, and the two row-sum identities make the reduced matrix a generator. The centered-residual lemmas are exactly the compatibility conditions for the blockwise Poisson corrector. When `u=v` and `w=z`, the rates no longer depend on the fast state, and the averaged generator agrees with the exact lumped chain at every scale. The general aggregation theorem still requires solving the corrector equations and proving convergence of the martingale problems as the fast scale diverges.
