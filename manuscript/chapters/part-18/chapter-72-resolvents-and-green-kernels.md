# Chapter 72 — Resolvents and Green Kernels

> **Audience.** This chapter assumes finite-state continuous-time chains, matrix exponentials, Feynman–Kac operators, and Poisson equations. It develops discounted occupation operators and their relationship to linear systems.

The transition semigroup (P_t=e^{tQ}) describes the chain at a fixed time. A resolvent averages that evolution over all future times with an exponential discount. It is simultaneously an integral operator, an inverse matrix, and an expected occupation measure. These three views support different proofs: semigroup arguments establish positivity, linear algebra solves boundary problems, and probability interprets entries as expected time spent in a state.

This chapter builds the finite-state theory and emphasizes a useful limiting relation: as the discount vanishes, the resolvent’s singular constant component separates from the centered Green operator that solves the Poisson equation.

## Learning objectives

By the end of the chapter, you should be able to:

- define the resolvent of a finite continuous-time generator;
- prove the discounted occupation and inverse-matrix formulas;
- derive the resolvent identity and parameter derivatives;
- interpret killed resolvents as Green kernels before absorption;
- recover the centered Poisson solution from a small-discount limit;
- formalize integral and matrix representations as separate interfaces.

## 1. The discounted occupation operator

Let Q be the row generator of a finite continuous-time Markov chain, and let (P_t=e^{tQ}). For α>0, define the resolvent
\[
  R_\alpha f=\int_0^\infty e^{-\alpha t}P_t f\,dt.
\]
For each state i, the value is the expected discounted accumulated reward:
\[
  (R_\alpha f)(i)=\mathbb E_i\left[
       \int_0^\infty e^{-\alpha t}f(X_t)\,dt\right].
\]
The integral converges because f is bounded on a finite state space and \(\alpha>0\). If \(f\geq0\), then \(R_\alpha f\geq0\); this positivity is immediate from the expectation representation and less transparent from a bare inverse matrix.

The time integral can be understood coordinatewise as a finite-dimensional vector-valued integral. For every t, P_t is stochastic, so \(\lVert P_t f\rVert_\infty\leq\lVert f\rVert_\infty\). Thus the integrand is bounded by \(e^{-\alpha t}\lVert f\rVert_\infty\), an integrable function. This supplies a simple domination proof and avoids introducing a general Banach-valued integral for a finite-dimensional problem.

The same estimate gives the operator bound
\[
  \lVert R_\alpha f\rVert_\infty\leq\frac{\lVert f\rVert_\infty}{\alpha}.
\]
The resolvent is order-preserving, and if \(0<\alpha<\beta\) then \(R_\alpha f\geq R_\beta f\) for every nonnegative f. Combining the bound with the resolvent identity gives
\[
  \lVert R_\alpha-R_\beta\rVert_{\infty\to\infty}
    \leq\frac{|\beta-\alpha|}{\alpha\beta}.
\]
These estimates are useful for continuity in the discount parameter and for validating finite approximations. They also give Lean-friendly intermediate goals: prove positivity first, then use the scalar integral of the discount to obtain the norm bound.

There is also a probabilistic random-horizon interpretation. Let Eα be independent of the chain and exponentially distributed with rate α. Its density is αe⁻αᵗ, so
\[
  \alpha R_\alpha f(i)=\mathbb E_i[f(X_{E_\alpha})].
\]
Thus αRα is a stochastic averaging operator: observe the chain at an independent exponential time. In particular, αRα preserves constants and is positive. This interpretation makes the large-discount limit intuitive—the observation time becomes short—and gives a probabilistic route to some resolvent inequalities.

## 2. The resolvent equation

Differentiate (e^{-\alpha t}P_t). Since (\frac{d}{dt}P_t=QP_t=P_tQ),
\[
  \frac{d}{dt}\left(e^{-\alpha t}P_t\right)
     =-(\alpha I-Q)e^{-\alpha t}P_t.
\]
Integrate from zero to T and let T tend to infinity. The boundary term at infinity vanishes because (e^{-\alpha T}P_T\to0), while the term at zero is I. Therefore
\[
  (\alpha I-Q)R_\alpha=I.
\]
In finite dimension a right inverse is a two-sided inverse, hence
\[
  R_\alpha=(\alpha I-Q)^{-1}.
\]
Equivalently, u=Rαf is the unique solution of the discounted Poisson equation
\[
  \alpha u-Qu=f.
\]

Invertibility also follows from the spectrum: eigenvalues of a Markov generator have nonpositive real part, so α-λ is nonzero for every eigenvalue λ when α>0. The semigroup-integral proof is often more useful in Lean because it constructs the inverse and establishes positivity at the same time. The matrix proof may be shorter when an inverse API is already available.

## 3. Worked example: a two-state resolvent

Let (0\to1) occur at rate a and (1\to0) at rate b, with a,b>0. Then
\[
  Q=\begin{pmatrix}-a&a\\b&-b\end{pmatrix},\qquad
  \alpha I-Q=
  \begin{pmatrix}\alpha+a&-a\\-b&\alpha+b\end{pmatrix}.
\]
The determinant is α(α+a+b), so
\[
  R_\alpha=\frac1{\alpha(\alpha+a+b)}
  \begin{pmatrix}\alpha+b&a\\b&\alpha+a\end{pmatrix}.
\]
Applied to f=(1,0), its first coordinate is ((\alpha+b)/(\alpha(\alpha+a+b))), the expected discounted time spent in state 0 starting from 0. Its second coordinate is (b/(\alpha(\alpha+a+b))), the corresponding occupation when starting from 1.

The row sums of Rα equal 1/α because (R_\alpha\mathbf1=\int_0^\infty e^{-\alpha t}\mathbf1\,dt). This is a valuable matrix sanity check. The nonnegative entries are another check on the signs: using Q-αI instead of αI-Q would reverse the inverse convention.

## 4. The resolvent identity

For positive α and β, the inverse representation gives
\[
  R_\alpha-R_\beta=(\beta-\alpha)R_\alpha R_\beta.
\]
Indeed, for invertible A and B, (A^{-1}-B^{-1}=A^{-1}(B-A)B^{-1}). Here (A=\alpha I-Q) and (B=\beta I-Q). The resolvents commute because both are functions of Q; the identity can also be written with the factors reversed.

The integral proof has a probabilistic interpretation. Multiplying two discounted occupation operators integrates over two ordered time intervals; the Markov semigroup property combines them into a single time variable with the difference of discount weights. The matrix proof is shorter, while the integral proof is useful for positivity and kernel estimates. Prove the algebraic identity once and use the representation appropriate to each application.

Repeated parameter differentiation gives
\[
  \frac{d^n}{d\alpha^n}R_\alpha
     =(-1)^n n! R_\alpha^{n+1}.
\]
The first derivative is (-R_\alpha^2). Differentiating the integral also shows
\[
  R_\alpha^{n+1}f
    =\frac1{n!}\int_0^\infty t^n e^{-\alpha t}P_t f\,dt.
\]
Thus powers of the resolvent encode polynomially weighted occupation times. In particular, derivatives of discounted rewards recover moments of the discount horizon.

### Uniformization expansion

Choose a uniformization rate \(\Lambda>0\) at least as large as every exit rate and set \(P=I+Q/\Lambda\). Then P is stochastic and
\[
  \alpha I-Q=(\alpha+\Lambda)I-\Lambda P.
\]
Since (\Lambda/(\alpha+\Lambda)<1), the geometric series converges in operator norm and gives
\[
  R_\alpha=\frac1{\alpha+\Lambda}
       \sum_{n=0}^\infty\left(\frac{\Lambda}{\alpha+\Lambda}\right)^nP^n.
\]
This expresses discounted occupation as a positive mixture of discrete-time iterates. It provides another proof of positivity and a computational approximation by truncating the series. The tail is bounded by a geometric remainder times \(\lVert f\rVert_\infty\), so the approximation has an explicit error estimate. This is a useful bridge between the resolvent and Chapter 56’s Poissonization.

The same equation is a contraction fixed point:
\[
  u=\frac{f}{\alpha+\Lambda}
       +\frac{\Lambda}{\alpha+\Lambda}Pu.
\]
Its contraction factor is \(\Lambda/(\alpha+\Lambda)<1\). Truncating after N iterations gives an error at most \((\Lambda/(\alpha+\Lambda))^{N+1}\lVert f\rVert_\infty/\alpha\). This is a practical proof pattern: establish the contraction and its fixed point abstractly, then derive the semigroup integral as a second representation. The iterative approximation uses only the discrete transition matrix and can be evaluated on a finite state type.

## 5. Killed resolvents and Green kernels

Let K be a finite subgenerator on a transient set S, with killing upon leaving S. For α≥0 define
\[
  G_\alpha=(\alpha I-K)^{-1}
    =\int_0^\infty e^{-\alpha t}e^{tK}\,dt.
\]
At α=0 the integral converges when killing occurs almost surely with an exponential tail; in finite irreducible transient systems with accessible killing this holds. The entry (G_\alpha(i,j)) is expected discounted time spent in j before killing, starting from i.

The row sum (G_0\mathbf1) is the vector of expected absorption times. More generally, (G_0f) gives expected accumulated reward before absorption. The first-step equation is (-Ku=f). For an event of hitting a boundary set A before a competing set B, restrict to the interior and place the boundary payoff into the right-hand side; the killed Green matrix then solves the corresponding Dirichlet problem.

The killed case is often easier than the conservative case at α=0: (-K) is invertible once absorption is certain, while (-Q) always has constants in its kernel. This is one reason potential theory frequently removes a target set and works with a killed chain.

### Worked example: two states before killing

Suppose transient states 1 and 2 move between one another at rates a and b, and are killed at rates κ₁ and κ₂. Then
\[
  K=\begin{pmatrix}-(a+\kappa_1)&a\\b&-(b+\kappa_2)\end{pmatrix}.
\]
At zero discount, the determinant of −K is
\[
  D=(a+\kappa_1)(b+\kappa_2)-ab
    =a\kappa_2+b\kappa_1+\kappa_1\kappa_2.
\]
When killing is accessible, D>0 and
\[
  G_0=(-K)^{-1}=\frac1D
  \begin{pmatrix}b+\kappa_2&a\\b&a+\kappa_1\end{pmatrix}.
\]
The expected absorption times are the row sums:
\[
  \mathbb E_1[T_\partial]=\frac{a+b+\kappa_2}{D},\qquad
  \mathbb E_2[T_\partial]=\frac{a+b+\kappa_1}{D}.
\]
The numerator reflects both internal movement rates and killing at the other state; the determinant records all routes by which mass can be removed. This example is a useful check of matrix orientation because the Green entry (G_0(1,2)=a/D) is generally different from (G_0(2,1)=b/D).

## 6. Resolvents and hitting boundary values

Let A be a target set and let τ_A be its first hitting time. For a boundary payoff g on A, define
\[
  u(i)=\mathbb E_i[e^{-\alpha\tau_A}g(X_{\tau_A})]
\]
for i outside A, with u=g on A. Conditioning on a short initial interval, or applying the discounted Dynkin formula up to τ_A, gives
\[
  (\alpha I-Q)u=0\quad\text{on }S\setminus A,
  \qquad u|_A=g.
\]
Equivalently, restrict Q to the complement and move rates into A to the right-hand side. The resulting killed resolvent solves the inhomogeneous interior system. At α=0 this is the ordinary harmonic hitting equation; for α>0 it discounts late arrivals.

For two disjoint boundary sets A and B, take g=1 on A and g=0 on B and kill on reaching either boundary. The solution is the Laplace transform of the event of hitting A first. Letting α decrease to zero recovers the hitting probability when the boundary is reached almost surely. This connects resolvents to the harmonic functions and maximum principles from Chapters 63 and 65.

The formal proof should establish uniqueness of the finite Dirichlet system. One route uses the maximum principle; another uses invertibility of the killed subgenerator. The probabilistic expectation then supplies existence, while uniqueness identifies it with the algebraic solution. If the target is never hit from a closed class, the undiscounted equation may not have a unique solution; either restrict to states that reach the boundary or keep α>0.

For the two-state chain of Section 3, let state 1 be the target and reward the discounted hit. Starting from 0, the hitting time is exponential with rate a, so
\[
  \mathbb E_0[e^{-\alpha\tau_1}]=\frac{a}{\alpha+a}.
\]
The boundary-value equation gives the same answer: u(1)=1 and αu(0)-a(u(1)-u(0))=0. This check connects the resolvent to a stopping-time transform without computing the full matrix exponential.

## 7. Reversibility and Green symmetry

Suppose Q is reversible with stationary probability π. Detailed balance implies (\pi(i)P_t(i,j)=\pi(j)P_t(j,i)) for every t. Integrating against (e^{-\alpha t}) gives
\[
  \pi(i)R_\alpha(i,j)=\pi(j)R_\alpha(j,i).
\]
Thus the resolvent is self-adjoint in the weighted inner product (\langle f,g\rangle_\pi=\sum_i\pi(i)f(i)g(i)). This is the operator version of the symmetry of expected discounted occupation flow. It can simplify capacity computations and spectral estimates.

The same statement holds for a reversible chain killed on a boundary set, using the restricted stationary weights on the interior; the killed subgenerator remains self-adjoint in that weighted space. In matrix coordinates, this is not ordinary symmetry unless the stationary distribution is uniform. A diagonal conjugation by √π makes the matrix symmetric and connects the resolvent to the Hermitian spectral APIs discussed in Chapter 70.

## 8. The small-discount limit and the Poisson equation

Assume Q is irreducible with stationary probability π. The constant component of the resolvent diverges like 1/α as α decreases to zero. More precisely,
\[
  R_\alpha f=\frac{\pi(f)}{\alpha}\mathbf1+Gf+o(1),
\]
where the centered Green operator is
\[
  Gf=\int_0^\infty(P_t f-\pi(f)\mathbf1)\,dt.
\]
Exponential convergence of a finite irreducible chain makes this integral converge. Applying Q under the integral yields
\[
  QGf=-(f-\pi(f)\mathbf1),\qquad \pi(Gf)=0.
\]
Thus Gf is precisely the centered Poisson solution used in Chapter 69.

An algebraic alternative avoids proving convergence of the improper integral. Decompose the function space as constants plus the π-centered subspace. On constants, Rα acts by multiplication by 1/α; on the centered subspace, −Q is invertible and Rα converges to −Q⁻¹. This decomposition makes the pole explicit and gives a finite-dimensional proof of the expansion.

At the other extreme, αRα converges to the identity as α→∞. Substitute s=αt to write
\[
  \alpha R_\alpha f=\int_0^\infty e^{-s}P_{s/\alpha}f\,ds.
\]
Strong continuity gives (P_{s/\alpha}f\to f) for each s, and contraction bounds the integrand by (e^{-s}\|f\|_\infty). Dominated convergence proves the limit. Thus large discount sees only the initial state, while small discount sees the stationary average plus a centered correction.

## 9. Formalization architecture

The useful interfaces are:

1. stochasticity and contraction of (P_t);
2. integrability of the discounted semigroup;
3. the integral identity ((\alpha I-Q)R_\alpha=I);
4. uniqueness for the discounted Poisson equation;
5. the resolvent identity and derivatives;
6. killed occupation interpretations;
7. the centered limit as α↓0.

The proof path is:

```text
transition semigroup ──> discounted integral ──> inverse equation
          │                      │                      │
          v                      v                      v
     positivity             occupation times      resolvent identities
                                                       │
                                                       v
                                           small-discount Poisson limit
```

For a concrete formalization, choose one matrix convention and keep it visible. With functions as column vectors and Q acting on the left, the equation is \((\alpha I-Q)u=f\); with probability distributions as row vectors, the transition law evolves on the other side. Many apparent transpose errors come from silently switching between these conventions. State the type of Q, the side on which it acts, and the meaning of matrix entries in the definitions rather than recovering them from later proofs.

Approximation also fits the interface. The uniformization series gives a finite sum and a certified tail bound, so a numerical result can be accompanied by a theorem of the form \(\lVert R_\alpha f-R_{\alpha,N}f\rVert_\infty\leq\varepsilon\). The proof splits into an exact geometric-series estimate and a computable bound on its scalar remainder. This separates the analytic argument from evaluation of finite matrix powers and makes the result usable even when the integral API is inconvenient.

Mathlib’s matrix inverse is defined through determinants and adjugates when the determinant is invertible. It is important to prove that αI−Q is nonsingular before simplifying with `⁻¹`; a matrix inverse operation by itself can return zero on singular matrices. The integral route provides a left inverse directly, after which finite-dimensional linear algebra gives nonsingularity.

## 10. Common failure modes

### The conservative generator is inverted at zero

(-Q) is singular because constants lie in its kernel. Center the problem or kill the chain.

### The sign of the resolvent equation is reversed

For a generator with nonpositive spectrum, use αI−Q, not Q−αI.

### The integral and inverse are identified without convergence

For α>0 use exponential discount and boundedness; at α=0 require killing or center the semigroup.

### A matrix inverse API is used without nonsingularity

Prove the determinant is nonzero or construct a genuine `Invertible` instance.

### A resolvent entry is called a transition probability

It is expected time occupancy and has units of time; row sums are 1/α, not 1.

## 11. Exercises

1. Prove the resolvent equation by integrating the derivative of (e^{-\alpha t}P_t).
2. Derive the two-state resolvent matrix and verify its row sums.
3. Prove the resolvent identity from the inverse formula.
4. Show that (R_\alpha f\geq0) whenever f is nonnegative.
5. Interpret the entries of a killed resolvent as discounted occupation times.
6. Derive expected absorption times from ((-K)u=\mathbf1).
7. Differentiate the resolvent and prove ∂αRα=−Rα².
8. Prove that the centered Green operator solves the Poisson equation.
9. Explain why the conservative resolvent diverges like π(f)/α as α decreases to zero.
10. Design a Lean interface connecting a semigroup integral with a matrix inverse.

## Summary

The finite-state resolvent is the exponentially discounted integral of a transition semigroup and the inverse of αI−Q. Its entries are discounted occupation times, its algebra yields resolvent identities and derivatives, and its killed version is a Green kernel before absorption. At small discount, the stationary constant mode creates a 1/α pole; after removing that mode, the limit is the centered Poisson solution. A formal proof should keep semigroup integrability, matrix nonsingularity, and probabilistic interpretation as distinct interfaces.

## Further reading

- Chapters 58–60 and 69 for generator identities, killed semigroups, spectral gaps, and Poisson response.
- [Mathlib’s nonsingular matrix inverse documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html).
- [Mathlib’s adjugate documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Adjugate.html).

## 12. Lean formalization: the two-state resolvent matrix

For rates `a` and `b` and discount `α`, the inverse of `αI - Q` has denominator `α(α+a+b)` and numerator entries `α+b`, `a`, `b`, and `α+a`. We verify the four matrix-product equations over the rationals, then check that each resolvent row sums to `1/α`. These identities formalize the inverse-matrix and discounted-occupation sanity checks from Section 3 without requiring a general matrix inverse theorem.

The earlier finite kernel calculation is retained.

```lean
import Book.Models.FiniteTwoState

open Book.Models.FiniteTwoState

def truncatedGreenMass : Nat :=
  rowMass identityKernel zero + rowMass flipKernel zero

theorem twoTermGreenCalculation : truncatedGreenMass = 4 := by decide
```

We state the entries explicitly. Positivity of the discount and nonnegative jump rates guarantees that the common denominator is positive, so every rational expression below is defined.

```lean
def resolvent00 (α a b : ℚ) : ℚ := (α + b) / (α * (α + a + b))
def resolvent01 (α a b : ℚ) : ℚ := a / (α * (α + a + b))
def resolvent10 (α a b : ℚ) : ℚ := b / (α * (α + a + b))
def resolvent11 (α a b : ℚ) : ℚ := (α + a) / (α * (α + a + b))

theorem resolvent_denominator_positive (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < α * (α + a + b) := by
  apply mul_pos hα
  positivity

theorem resolvent_left_product_00 (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (α + a) * resolvent00 α a b - a * resolvent10 α a b = 1 := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent00 resolvent10
  field_simp [hα', ne_of_gt hsum]
  ring

theorem resolvent_left_product_01 (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (α + a) * resolvent01 α a b - a * resolvent11 α a b = 0 := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent01 resolvent11
  field_simp [hα', ne_of_gt hsum]
  ring

theorem resolvent_left_product_10 (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    -b * resolvent00 α a b + (α + b) * resolvent10 α a b = 0 := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent00 resolvent10
  field_simp [hα', ne_of_gt hsum]
  ring

theorem resolvent_left_product_11 (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    -b * resolvent01 α a b + (α + b) * resolvent11 α a b = 1 := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent01 resolvent11
  field_simp [hα', ne_of_gt hsum]
  ring

theorem resolvent_row_sum_zero (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    resolvent00 α a b + resolvent01 α a b = 1 / α := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent00 resolvent01
  field_simp [hα', ne_of_gt hsum]
  ring

theorem resolvent_row_sum_one (α a b : ℚ)
    (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    resolvent10 α a b + resolvent11 α a b = 1 / α := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hsum : 0 < α + a + b := by positivity
  unfold resolvent10 resolvent11
  field_simp [hα', ne_of_gt hsum]
  ring
```

The four product equations certify that the displayed matrix is a two-sided inverse candidate for `αI-Q` on the left. The row-sum identities show that applying the resolvent to the constant observable gives `1/α`, exactly the total discounted time. The integral representation, positivity for arbitrary nonnegative observables, and its convergence remain separate semigroup results.
