# Chapter 69 — Linear Response for Finite Markov Chains

> **Audience.** This chapter assumes finite irreducible chains, stationary distributions, generators, and the Poisson equation. It studies differentiable families of transition rates and derives formulas for the sensitivity of stationary expectations.

In applications, transition rates often depend on a parameter: temperature, a control input, a mutation probability, or a model coefficient. A stationary expectation then changes with that parameter. Differentiating the stationary equations produces a useful identity, but the resulting linear system is singular because generators annihilate constants. The Poisson equation resolves exactly this singularity by centering the observable.

This chapter develops the finite-dimensional response formula, checks it in a two-state model, and connects analytic differentiation to the tree formula from Chapter 68. It also shows where reversibility enters quantitative sensitivity bounds and where a Lean proof can remain purely algebraic.

## Learning objectives

By the end of the chapter, you should be able to:

- differentiate the stationary equation for a smooth generator family;
- solve the centered Poisson equation with a normalization condition;
- express a stationary-expectation derivative as a generator perturbation paired with a Poisson solution;
- compute and verify the formula in a parameterized two-state chain;
- derive a reversible sensitivity bound from the spectral gap;
- separate differentiability, nullspace, and probabilistic arguments in Lean.

## 1. A differentiable family of generators

Let S be finite and let \(Q_\theta\) be a family of row generators for θ in an open interval I. Assume each off-diagonal rate is differentiable in θ, every row sums to zero, and the chain is irreducible for all θ in the interval. There is then a unique stationary probability row vector πθ satisfying
\[
  \pi_\theta Q_\theta=0,\qquad \sum_x\pi_\theta(x)=1.
\]
For a finite irreducible chain, this vector depends differentiably on θ locally. One proof selects a normalization equation and solves an invertible |S|-by-|S| linear system; another uses the tree formula of Chapter 68, where each tree weight is a finite product of differentiable rates.

The irreducibility assumption should hold on a neighborhood of the parameter at which the derivative is taken. If the support graph changes exactly at that parameter, stationary classes can appear or disappear and the normalized solution may fail to be differentiable. A robust theorem assumes a fixed strongly connected support with positive rates on its edges throughout the interval; weaker hypotheses can be handled locally when continuity keeps a chosen irreducible spanning subgraph positive.

Write a dot for differentiation at a fixed parameter value. Differentiating stationarity and normalization gives
\[
  \dot\pi Q+\pi\dot Q=0,\qquad \sum_x\dot\pi(x)=0.
\]
The first equation alone does not determine \(\dot\pi\): Q is singular, and adding a multiple of π to a solution of the left linear equation leaves its product with Q unchanged. The normalization derivative fixes that ambiguity.

Since every row sum of \(Q_\theta\) is zero, differentiating it also gives \(\dot Q_\theta\mathbf1=0\). This compatibility condition is what allows the differentiated stationary equation to have a solution with zero total mass.

## 2. The centered Poisson equation

Fix an observable g:S→ℝ and let μ=πg=∑_xπ(x)g(x). The centered observable (g-\mu\mathbf 1) has stationary mean zero. Therefore there exists h solving
\[
  Qh=-(g-\mu\mathbf 1).
\]
The solution is unique up to an additive constant. Fix it by requiring πh=0. The centered subspace {f:πf=0} is invariant under Q; irreducibility implies Q has trivial kernel on this subspace, so its restriction is invertible.

The minus sign is a convention chosen to make the response formula positive in the form below. Some texts define the Poisson equation as \(-Qh=g-\mu\), which is the same equation. When porting a theorem between generator conventions, check both whether generators act on row or column vectors and which sign is used for the Laplacian.

For a finite chain, the existence result is linear algebra. The range of Q on functions is the subspace of π-mean-zero functions: it is contained there because πQ=0, and equality follows by rank-nullity since Q has one-dimensional kernel. No martingale theorem is needed to state or solve this equation.

One computational realization removes the singularity by replacing one equation with the normalization πh=0. Choose a reference state r, solve the Poisson equation at all states except r, and impose h(r)=0; afterward subtract the π-mean to obtain the centered solution. Alternatively, restrict Q to the centered subspace and use its inverse. The first method uses an ordinary square matrix indexed by all but one state; the second makes uniqueness canonical and is better for abstract operator theorems. Prove equivalence once instead of switching normalizations mid-proof.

## 3. The linear-response identity

Differentiate the stationary expectation μθ=πθg for fixed g. Since \(\dot\pi\) has total mass zero,
\[
  \dot\mu=\dot\pi g=\dot\pi(g-\mu\mathbf1).
\]
Use the Poisson equation and the differentiated stationarity equation:
\[
  \dot\mu=-\dot\pi Qh=\pi\dot Qh.
\]
Thus
\[
  \boxed{\displaystyle
  \frac{d}{d\theta}\pi_\theta(g)
       =\pi_\theta\bigl(\dot Q_\theta h_\theta\bigr),
  \quad Q_\theta h_\theta=-(g-\pi_\theta g),\quad
  \pi_\theta h_\theta=0.}
\]
The derivative of the stationary law has disappeared. The response is the stationary average of the perturbation operator applied to the Poisson solution.

This identity is particularly useful when the state space is large but solving one Poisson equation is easier than differentiating every stationary probability. It also makes the role of slow mixing visible: if Q has a small spectral gap, h can be large, so a small rate perturbation may produce a substantial change in stationary expectation.

If the observable also depends on θ, the product rule gives
\[
  \frac{d}{d\theta}\pi_\theta(g_\theta)
   =\pi_\theta(\dot g_\theta)
      +\pi_\theta(\dot Q_\theta h_\theta).
\]
The first term is the direct change in what is measured; the second is the indirect change in the stationary distribution.

The same statement works for a vector parameter θ∈ℝ^m. For a direction v, replace the scalar derivative \(\dot Q\) by the directional derivative \(DQ_\theta[v]\); then
\[
  D\bigl(\pi_\theta(g)\bigr)[v]
     =\pi_\theta\bigl(DQ_\theta[v]h_\theta\bigr).
\]
Taking v to be each coordinate vector gives the gradient. This directional form is usually the cleanest theorem in Lean because it avoids expanding a gradient into m coordinates and can be reused for path derivatives, optimization, and parameter sensitivities. Differentiability of the stationary law is still required, but the algebraic identity itself is linear in the perturbation direction.

## 4. Worked example: a two-state chain

Let the rate from 0 to 1 be a(θ)>0 and from 1 to 0 be b(θ)>0. The stationary probability of state 1 is
\[
  \pi_\theta(1)=\frac{a}{a+b},\qquad
  \pi_\theta(0)=\frac{b}{a+b}.
\]
Take \(g=\mathbf1_{\{1\}}\), so \(\mu=a/(a+b)\). Write \(s=a+b\). The Poisson equation at state 0 is \(a(h_1-h_0)=\mu\), giving \(h_1-h_0=1/s\). At state 1 it gives the same difference. The normalization πh=0 fixes
\[
  h_0=-\frac{a}{s^2},\qquad h_1=\frac{b}{s^2}.
\]
The derivative generator has off-diagonal rates \(\dot a\) and \(\dot b\) and diagonal entries −\(\dot a\) and −\(\dot b\). Therefore
\[
  \pi\dot Qh
   =\frac{b}{s}\dot a\,(h_1-h_0)
      +\frac{a}{s}\dot b\,(h_0-h_1)
   =\frac{b\dot a-a\dot b}{s^2}.
\]
Direct differentiation of (a/(a+b)) gives the same expression. This small calculation is a strong sign and orientation check for any general proof.

It also shows why the off-diagonal rate derivative alone is not the whole matrix \(\dot Q\): the diagonal must be the negative row sum. If the diagonal derivative is omitted, \(\dot Q\) no longer annihilates constants and the response identity fails.

## 5. Worked example: temperature-dependent two-spin law

Consider the two-spin Gibbs distribution from Chapter 64, with aligned-spin probability depending on the parameter β. There are two aligned states of energy −J and two opposed states of energy J. The probability of alignment is
\[
  p_\beta=\frac{e^{\beta J}}{e^{\beta J}+e^{-\beta J}}
          =\frac{1+\tanh(\beta J)}2.
\]
For the observable g that records whether the spins agree, direct differentiation yields
\[
  \frac{d}{d\beta}\mathbb E_{\pi_\beta}[g]
      =\frac{J}{2}\,\operatorname{sech}^2(\beta J).
\]
If the spin dynamics are heat-bath updates, their rates also depend on β. The response formula computes the derivative through π\(\dot Q\)h, while the explicit Gibbs expression provides an independent check. This is a useful example of two representations of the same sensitivity: a static partition-function derivative and a dynamic generator perturbation.

The distinction matters in larger models. Differentiating a partition function may be expensive, while a Poisson equation can exploit the generator’s sparse local structure. Conversely, when a closed-form Gibbs family is available, it can validate the signs and normalization in the formal response theorem.

## 6. Reversible bounds from the spectral gap

Assume Q is reversible with respect to the probability π and has spectral gap γ>0. On the centered subspace, the inverse of −Q has operator norm at most (1/\gamma). The Poisson solution therefore satisfies
\[
  \|h\|_{L^2(\pi)}\leq\frac{\|g-\pi g\|_{L^2(\pi)}}{\gamma}
       =\frac{\sqrt{\operatorname{Var}_\pi(g)}}{\gamma}.
\]
Using Cauchy–Schwarz and the \(L^2(\pi)\)-operator norm of \(\dot Q\) gives
\[
  \left|\frac{d}{d\theta}\pi_\theta(g)\right|
    \leq \|\dot Q\|_{2\to2}
       \frac{\sqrt{\operatorname{Var}_\pi(g)}}{\gamma}.
\]
This estimate is schematic in one respect: if the Hilbert space itself is parameterized by πθ, compare norms at the fixed parameter value where the derivative is taken. For nonreversible generators, replace the spectral-gap inverse estimate by a bound on the centered resolvent or use a coercivity estimate for the symmetric part.

This result connects Chapters 60 and 69. A spectral gap controls both convergence to equilibrium and the stability of equilibrium expectations. Slow relaxation makes response larger because the Poisson equation must accumulate drift over a longer time scale.

### Response as an integrated semigroup effect

For a finite irreducible chain, the centered semigroup decays exponentially. Therefore the Poisson solution can also be written
\[
  h=\int_0^\infty(P_tg-\pi g)\,dt,
\]
where \(P_t=e^{tQ}\) acts on observables. Applying Q under the integral gives
\[
  Qh=\int_0^\infty\frac{d}{dt}(P_tg-\pi g)\,dt
      =\pi g-g=-(g-\pi g).
\]
Substitution into the response formula yields
\[
  \frac{d}{d\theta}\pi_\theta(g)
    =\int_0^\infty\pi_\theta(\dot Q_\theta P_tg)\,dt,
\]
because \(\dot Q\) annihilates constants. The identity expresses sensitivity as a cumulative effect over the chain’s relaxation time. It is not automatically a covariance formula; special perturbation structures can rewrite the integrand as a correlation, but that requires additional algebra.

The integral representation is conceptually useful, while the finite linear system is usually easier to formalize. To justify the improper integral, use finite-state exponential convergence and integrate coordinatewise. A Lean proof can first establish the semigroup solution on ([0,T]), then pass to the limit using a uniform exponential bound. Keeping this as a corollary prevents analytic convergence details from obscuring the algebraic response identity.

## 7. A second route through tree weights

Chapter 68 gives πθ(i)=τθ(i)/∑_jτθ(j), where each τ is a finite sum of products of rates. If the rates are differentiable, differentiate this quotient:
\[
  \dot\pi(i)=\frac{\dot\tau(i)Z-\tau(i)\dot Z}{Z^2},
  \qquad Z=\sum_j\tau(j).
\]
The derivative \(\dot\tau\)(i) is itself a sum over rooted trees, with each product differentiated by the finite product rule. This gives a fully explicit expression for stationary sensitivity in terms of the change in each transition rate.

The tree route is attractive for symbolic formulas and very small chains. Its cost grows with the number of directed spanning trees. The Poisson route instead solves a linear equation on the state space and may be much more efficient computationally. The two derivations should agree, and their equality is a rich finite algebra exercise: differentiate the tree expression, then show it solves the differentiated stationary equation with zero total mass.

For the oriented three-cycle of Chapter 68, vary a while holding b and c fixed. With \(Z=ab+bc+ca\), differentiation of the tree weights gives
\[
  \dot\pi_0=-\frac{bc(b+c)}{Z^2},\qquad
  \dot\pi_1=\frac{bc^2}{Z^2},\qquad
  \dot\pi_2=\frac{b^2c}{Z^2}.
\]
The derivatives sum to zero, as required by normalization. This is a useful nonreversible test case for a general implementation: it checks the tree orientation, the quotient rule, and the normalization equation without any detailed-balance simplification.

### Perturbations that only change the clock

Suppose \(Q_\theta=s(\theta)Q_0\) with \(s(\theta)>0\). This rescales every holding time but leaves the stationary distribution unchanged. The response formula predicts zero: \(\dot Q=s'Q_0\), and for the Poisson solution \(Q_0h=-(g-\pi g)\),
\[
  \pi\dot Qh=s'\pi Q_0h=-s'\pi(g-\pi g)=0.
\]
This is a concise symbolic test of the identity and a useful modeling distinction. Perturbing relative rates changes equilibrium weights; uniformly speeding up every transition changes only the time scale. A theorem that fails this invariance likely has a sign, diagonal, or row/column convention error.

## 8. Lean proof architecture

The formal development can be divided into four modules.

**Parameter calculus.** Prove differentiability of each matrix entry, finite sums, and products. Establish differentiability of the normalized stationary solution either from an invertible linear system or from the tree formula.

**Stationary linear algebra.** Package the equations πQ=0 and π 1=1. Prove that the restriction of Q to centered observables is invertible under irreducibility. This is the point where a rank theorem and finite-dimensional subspace API are useful.

**Poisson solver.** Define h as the unique centered solution of \(Qh=-(g-\pi g)\). State the solution theorem independently of differentiation. The response proof then uses only substitution and finite-sum rearrangement.

**Derivative identity.** Differentiate the stationary equation coordinatewise, multiply the differentiated equation by h, and use the Poisson equation. Keep the row-vector/column-function convention in the theorem statement to avoid transposing the wrong factor.

The dependency path is:

```text
smooth rates ──> smooth normalized stationary law ──> differentiated stationarity
                                                             │
centered observable ──> Poisson solution ────────────────────┘
                                                             v
                                                   response identity
                                                             │
                                             reversible gap gives a bound
```

No sample-path construction is required for the core derivative formula. If the application interprets the derivative as a long-time covariance or integrated correlation, that probabilistic representation is a further theorem and may require integrability and semigroup convergence assumptions.

## 9. Common failure modes

### The singular stationary system is inverted directly

Q has constants in its right kernel. Center the observable and fix a normalization before using an inverse.

### The diagonal rate derivative is omitted

The derivative generator must still have row sums zero.

### A Poisson equation has no centering condition

Its right-hand side must have stationary mean zero, and the solution is unique only up to a constant.

### The sign convention is copied without checking

Verify the formula on the two-state chain; generator and Laplacian signs vary across texts.

### Reversibility is used in a nonreversible theorem

The response identity only needs finite irreducibility and differentiability. Reversibility enters the spectral-gap bound.

### Parameter dependence of the observable is forgotten

Include the direct term π\(\dot g\) when g itself changes with the parameter.

## 10. Exercises

1. Differentiate πQ=0 and π1=1 for a finite generator family.
2. Prove the centered range characterization for an irreducible generator.
3. Derive the linear-response identity from the normalized Poisson equation.
4. Verify the two-state formula for \(g=\mathbf1_{\{1\}}\).
5. Compute sensitivity for a two-state chain with \(a(\theta)=e^\theta\) and constant b.
6. Add the direct derivative term for a parameter-dependent observable.
7. Derive the reversible spectral-gap bound on ∥h∥.
8. Differentiate a three-state tree formula and compare it with the Poisson response.
9. Explain which step fails if irreducibility is lost and the stationary law is not unique.
10. Design a Lean API for a differentiable family of finite matrices with a normalized left kernel vector.

## Summary

For a differentiable family of finite irreducible generators, the stationary law satisfies a differentiated linear system. Centering an observable yields a Poisson equation whose solution removes the derivative of the stationary distribution: the response is π\(\dot Q\)h. Reversibility and a spectral gap bound the size of h, while the tree theorem offers an explicit but combinatorial alternative. A clean formalization isolates matrix differentiation, centered invertibility, Poisson solutions, and the final algebraic identity.

## Further reading

- Chapters 58, 60, and 68 for generator martingales, spectral gaps, and stationary tree weights.
- Chapter 64 for the parameterized two-spin heat-bath model.
