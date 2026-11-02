# Chapter 60 — Spectral Gaps and Continuous-Time Mixing

> **Audience.** This chapter assumes familiarity with finite-state Markov chains, reversible generators, inner products, and matrix exponentials. It connects a generator’s spectral gap to exponential convergence toward equilibrium.

Finite-state continuous-time chains often converge to a stationary law. Reversibility makes the convergence rate accessible through linear algebra: after changing to the stationary weighted inner product, the generator becomes self-adjoint. Its nonzero eigenvalues describe the decay rates of mean-zero observables.

The spectral-gap argument has two useful forms. The eigenvector form diagonalizes the generator and reads the decay directly from its eigenvalues. The energy form proves a differential inequality for the squared norm and integrates it. The second often gives a better theorem interface: a Poincaré inequality is enough, even when the proof does not need an explicit eigenbasis.

## Learning objectives

By the end of the chapter, you should be able to:

- express reversibility as self-adjointness in a weighted inner product;
- derive the Dirichlet form associated with a generator;
- state a spectral gap as a Poincaré inequality;
- prove exponential decay in the stationary L² norm;
- convert L² decay into a total-variation mixing bound;
- use a finite-dimensional spectral theorem without assuming Mathlib has a CTMC convergence theorem.

## 1. The stationary weighted inner product

Let S be finite, Q a generator, and π a stationary probability distribution with π(x)>0 for every x. Define
\[
  \langle f,g\rangle_\pi=\sum_x\pi(x)f(x)g(x),
  \qquad
  \|f\|_{2,\pi}^2=\langle f,f\rangle_\pi.
\]
The mean of f under π is \(\pi f=\sum_x\pi(x)f(x)\), and its variance is
\[
  \operatorname{Var}_\pi(f)=\|f-\pi f\|_{2,\pi}^2.
\]

Detailed balance for the generator says
\[
  \pi(x)q_{xy}=\pi(y)q_{yx}\qquad(x\ne y).
\]
It implies that Q is self-adjoint in this weighted inner product:
\[
  \langle f,Qg\rangle_\pi=\langle Qf,g\rangle_\pi.
\]
The equality is a finite reindexing of the double sum and uses detailed balance to exchange x and y. Stationarity alone does not imply this symmetry.

The constant functions lie in the kernel of Q because every generator row sums to zero. If the chain is irreducible, constants are the only functions in the kernel. In that case, the nonconstant directions describe transient deviations from equilibrium.

## 2. The Dirichlet form

Define the Dirichlet form by
\[
  \mathcal E(f,g)=-\langle f,Qg\rangle_\pi.
\]
For a reversible generator, symmetrizing the finite sum gives
\[
  \mathcal E(f,g)
   =\frac12\sum_{x,y}\pi(x)q_{xy}
        \bigl(f(y)-f(x)\bigr)\bigl(g(y)-g(x)\bigr).
\]
In particular,
\[
  \mathcal E(f,f)
   =\frac12\sum_{x,y}\pi(x)q_{xy}
        \bigl(f(y)-f(x)\bigr)^2\geq0.
\]
Thus −Q is positive semidefinite in the stationary inner product.

The Dirichlet form measures how much an observable changes across edges that carry transition rate. A function nearly constant along high-rate edges has small energy. If the rate graph is connected, a function with zero energy must be constant, which is the quadratic-form reflection of irreducibility.

The factor one-half avoids counting each undirected edge twice. A formal proof should decide whether the double sum ranges over all ordered pairs or only over distinct pairs. Since q_xx multiplies a zero difference, including the diagonal is harmless, but spelling this out can simplify sum manipulations.

## 3. Spectral gap and Poincaré inequality

A positive number γ is a spectral-gap lower bound if
\[
  \mathcal E(f,f)\geq
    \gamma\,\operatorname{Var}_\pi(f)
\]
for every function f. Equivalently, on the subspace of mean-zero functions, the self-adjoint operator −Q is bounded below by γ.

When Q is irreducible and reversible on a finite state space, such a positive γ exists. In an eigenbasis, Q has eigenvalue zero on constants and strictly negative eigenvalues on the orthogonal complement. The smallest absolute value among those nonzero eigenvalues is the optimal spectral gap.

The Poincaré formulation is often preferable to defining γ as a minimum over eigenvalues. It avoids choices about eigenvalue ordering and gives exactly the inequality needed in the convergence proof. A separate theorem can later identify the best constant with the smallest positive eigenvalue of −Q.

If the chain is reducible, the kernel of Q contains functions constant on each closed component. Then a global inequality with positive γ and variance around a single stationary law fails unless additional restrictions are imposed. Irreducibility, positivity of π, and the mean-zero subspace should be explicit in the theorem statement.

## 4. Exponential decay in L²

Let f be an observable and put
\[
  g_t=P_t f-\pi f.
\]
Stationarity implies that g_t has mean zero for every t. Differentiate its squared norm:
\[
\begin{aligned}
  \frac{d}{dt}\|g_t\|_{2,\pi}^2
    &=2\langle g_t,Qg_t\rangle_\pi\\
    &=-2\mathcal E(g_t,g_t)\\
    &\leq-2\gamma\|g_t\|_{2,\pi}^2.
\end{aligned}
\]
The scalar differential inequality yields
\[
  \|P_t f-\pi f\|_{2,\pi}
    \leq e^{-\gamma t}\|f-\pi f\|_{2,\pi}.
\]
This is the basic continuous-time mixing estimate for observables.

The eigenvector proof reaches the same result by writing f−πf as a sum of eigenvectors. Each component with eigenvalue −λ is multiplied by e^{-λt}; the smallest λ controls the slowest decay. The energy proof needs only the Poincaré inequality and a derivative of the norm, so it can be easier to generalize to operators without an explicitly computed eigenbasis.

In a formal proof, take care at points where the norm is zero if differentiating the norm directly. Differentiating its square avoids division by zero. Then compare the nonnegative function \(u(t)=\|g_t\|^2\) with the solution of \(u'=-2\gamma u\), using an elementary differential inequality theorem.

More precisely, choose an orthonormal basis of eigenfunctions
\(\phi_0,\phi_1,\ldots\) with \(\phi_0=\mathbf 1\), and write
\[
  f=\pi f+\sum_{k\geq1}c_k\phi_k,\qquad Q\phi_k=-\lambda_k\phi_k.
\]
Then
\[
  P_t f-\pi f=\sum_{k\geq1}c_ke^{-\lambda_k t}\phi_k,
  \qquad
  \|P_t f-\pi f\|_{2,\pi}^2
    =\sum_{k\geq1}c_k^2e^{-2\lambda_k t}.
\]
The gap bound replaces each \(\lambda_k\) by its common lower bound γ.
The expansion also shows when the estimate is sharp: an observable with a
nonzero coefficient on a gap eigenfunction decays at exactly the slowest
rate asymptotically. If its projection onto that eigenspace vanishes, its
actual decay can be faster.

This spectral expansion distinguishes a global operator bound from the
behavior of one selected observable. A theorem claiming a uniform rate for
all centered functions needs the smallest nonzero eigenvalue. A computation
for one function may only require the eigenvalues that appear in its
expansion.

## 5. From L² decay to total variation

This section uses the half-normalized probability distance
\(d_{\mathrm{TV}}=\frac12\sum_x|\mu(x)-\nu(x)|\). Mathlib’s tvDist is twice
this value, as explained in Chapter 48. Thus a bound stated here for
\(d_{\mathrm{TV}}\) becomes a bound with twice the right-hand side when
written using tvDist.

Suppose μ is an initial law and define its density relative to π by
\[
  h_0(x)=\frac{\mu(x)}{\pi(x)}.
\]
Detailed balance implies that the density at time t is \(h_t=P_t h_0\). Therefore the L² estimate applies to h₀−1. On a finite space,
\[
\begin{aligned}
  \|\mu P_t-\pi\|_{\mathrm{TV}}
   &=\frac12\sum_y\pi(y)|h_t(y)-1|\\
   &\leq\frac12\|h_t-1\|_{2,\pi}\\
   &\leq\frac12e^{-\gamma t}\|h_0-1\|_{2,\pi}.
\end{aligned}
\]
The first inequality is Cauchy–Schwarz under the probability law π.

For a chain started at a single state x, the initial density is \(h_0(y)=\mathbf 1_{\{y=x\}}/\pi(x)\), and
\[
  \|h_0-1\|_{2,\pi}^2=\frac1{\pi(x)}-1.
\]
Thus
\[
  \|\delta_xP_t-\pi\|_{\mathrm{TV}}
    \leq\frac12
       \sqrt{\frac1{\pi(x)}-1}\,e^{-\gamma t}.
\]
The prefactor records how concentrated the initial state is relative to equilibrium. A small stationary mass π(x) can make this bound loose at early times even when the eventual exponential rate is sharp.

Reversibility is used twice in this route: it gives self-adjointness and it lets the density evolve by the same operator P_t. Without reversibility, one can still study convergence, but the adjoint semigroup and singular values may replace the simple eigenvalue argument.

Let \(\pi_{\min}=\min_x\pi(x)\). Taking the worst initial state gives the uniform estimate
\[
  \sup_x\|\delta_xP_t-\pi\|_{\mathrm{TV}}
  \leq \frac12\sqrt{\frac1{\pi_{\min}}-1}\,e^{-\gamma t}.
\]
Consequently, to make this distance at most ε, it is enough to take
\[
  t\geq\frac1\gamma
      \log\!\left(\frac{\sqrt{\pi_{\min}^{-1}-1}}{2\varepsilon}\right)
\]
whenever the logarithm is positive. This is an upper bound on the mixing
time, not an exact answer. It separates the exponential relaxation scale
1/γ from the stationary-mass prefactor.

The estimate can be conservative. L² controls the worst density
concentration and may lose information about the geometry of the starting
state. Coupling, conductance, or comparison arguments can yield better
finite-time constants, while the spectral gap still captures the eventual
slowest exponential mode.

## 6. Worked example: the complete graph

Take n states and let the jump rate from each state to each distinct state be r>0. The stationary law is uniform. For any f,
\[
  (Qf)(x)=r\sum_{y\ne x}(f(y)-f(x))
         =nr\bigl(\pi f-f(x)\bigr).
\]
Every mean-zero function is therefore an eigenfunction with eigenvalue −nr. The spectral gap is nr, and the semigroup has the exact form
\[
  P_t f=\pi f+e^{-nrt}(f-\pi f).
\]
The Poincaré inequality is an equality for every mean-zero f.

This example is useful for checking the normalization in the Dirichlet form. The total rate out of a state is (n−1)r, but the nonconstant eigenvalue is −nr. Confusing exit rate with spectral gap would miss the contribution of transitions into all n−1 other states.

For a Lean development, represent the generator using the uniform off-diagonal rate and prove the formula for Qf by finite-sum algebra. Then the spectral-gap theorem reduces to a scalar identity on the mean-zero subspace; no general diagonalization is needed for this special model.

## 7. Worked example: a two-state chain

For rates a>0 from 0 to 1 and b>0 from 1 to 0, the stationary law is
\[
  \pi(0)=\frac{b}{a+b},\qquad
  \pi(1)=\frac{a}{a+b}.
\]
The only nonconstant direction is spanned by a centered indicator. Direct substitution into Q shows that it has eigenvalue −(a+b). Hence the spectral gap is a+b, and every centered observable obeys the exact decay law
\[
  P_t f-\pi f=e^{-(a+b)t}(f-\pi f).
\]
The transition formulas from Chapter 55 are the coordinate version of this same equation.

The example also illustrates weighted symmetry. The two rates need not be equal, so Q is not symmetric as an ordinary matrix. It is self-adjoint under the π-weighted inner product because
\[
  \pi(0)a=\pi(1)b.
\]
This is why a similarity transform or weighted inner product is needed before invoking a Euclidean matrix spectral theorem.

## 8. Conjugating to a symmetric matrix

Let D be the diagonal matrix with D(x,x)=π(x). Since π is strictly positive, D has a positive square root. Define
\[
  H=D^{1/2}QD^{-1/2}.
\]
Detailed balance implies H is symmetric. The operators Q and H are similar, so they have the same eigenvalues. The Euclidean spectral theorem for real symmetric or Hermitian matrices then supplies an orthonormal eigenbasis for H.

The transformed constant direction is the vector with coordinates \(\sqrt{\pi(x)}\). Mean-zero functions correspond to vectors orthogonal to this direction. Irreducibility shows the zero eigenvalue is simple; the remaining eigenvalues are negative. A lower bound on the eigenvalues of −H away from zero is exactly a spectral-gap bound.

This route maps a probability-weighted statement into a standard finite-dimensional linear-algebra theorem. The main formal obligations are constructing square roots of the positive diagonal entries, proving H symmetric from detailed balance, and transporting inner products and norms through the similarity. For larger developments, the weighted inner-product route may avoid repeated matrix conjugations; for explicit eigenvalue calculations, the symmetric-matrix route can be more convenient.

## 9. Relating discrete and continuous-time gaps

Uniformization writes Q=Λ(R−I), where R is a reversible stochastic matrix
when Q is reversible. If the eigenvalues of R are ordered
1=θ₁≥θ₂≥⋯≥θₙ≥−1, the corresponding eigenvalues of Q are
Λ(θᵢ−1). Therefore the continuous-time spectral gap is
\[
  \gamma=\Lambda(1-\theta_2).
\]
This formula links Chapter 56's Poissonization to the long-time estimate in
this chapter.

There is an important difference from a common discrete-time convergence
parameter. Discrete-time L² convergence can depend on the largest absolute
value of a nonconstant eigenvalue, because an eigenvalue near −1 produces
slow oscillation. In continuous time, the mode θᵢ contributes the factor
\[
  e^{\Lambda(\theta_i-1)t}.
\]
A negative θᵢ gives faster decay, not an oscillation. The continuous-time
gap is determined by the largest nonconstant eigenvalue, not by its largest
absolute value.

Uniformization therefore provides more than a computational identity. It
converts the eigenvalues of a discrete kernel into decay rates of the
continuous semigroup. A formal proof can reuse a discrete spectral theorem
for R, verify that detailed balance is preserved, and map each eigenvalue
through the affine relation above.

## 10. Lean formalization strategy

Build the proof in layers:

1. Establish π is positive, normalized, and invariant.
2. Define the weighted inner product and prove Q is self-adjoint.
3. Derive the Dirichlet-form identity and nonnegativity.
4. State the Poincaré inequality as a reusable hypothesis or prove it from the spectrum.
5. Differentiate the squared L² norm along the semigroup and solve the scalar differential inequality.
6. Convert the resulting norm bound to total variation using Cauchy–Schwarz.

Mathlib includes a spectral theorem for finite Hermitian matrices and matrix-exponential identities. These support the finite-dimensional linear algebra, but the transformation from detailed balance to a symmetric operator, the identification of the gap, and the probability-distance bound remain application-specific. Do not assume the library provides a single theorem named for continuous-time Markov-chain mixing.

The Poincaré route can make the main theorem abstract. State it for a finite-dimensional inner-product space, a self-adjoint dissipative operator, and a lower quadratic-form bound on the invariant complement. Then instantiate that theorem with the reversible generator. This separates general differential analysis from Markov-specific bookkeeping.

For total variation, define the convention explicitly: on a finite state space it is one half of the sum of absolute differences. Prove the density identity under reversibility before applying Cauchy–Schwarz. If the project instead defines total variation as a supremum over events, prove the equivalence of the two finite-state formulas once and reuse it.

## 11. Common failure modes

### Reversibility is replaced by stationarity

Stationarity gives invariance; detailed balance gives self-adjointness. The spectral argument needs the latter or another substitute.

### The spectral gap is confused with an exit rate

The slowest decay is determined by the smallest nonzero eigenvalue magnitude, not by the largest rate leaving a state.

### Constants are not removed

The generator always has constants in its kernel. A positive lower bound applies only to the mean-zero subspace.

### The weighted matrix is called symmetric without proof

Q is generally nonsymmetric in standard coordinates. Prove weighted self-adjointness or conjugate by the stationary square-root matrix.

### L² convergence is identified with total variation without a bound

Use the density formula and Cauchy–Schwarz, including the factor one-half in the finite-state total-variation convention.

The one-state chain is a harmless but useful boundary case: there is no
nonconstant subspace and the distance to equilibrium is always zero. Avoid
defining the gap as a minimum over an empty set without specifying a
convention. State the convergence theorem for at least two states, or handle
the trivial chain separately before introducing the spectral gap.

## 12. Exercises

1. Derive the Dirichlet-form formula from detailed balance.
2. Prove that zero Dirichlet energy forces f to be constant on each connected component of the rate graph.
3. Show that a Poincaré inequality gives exponential decay of the squared L² norm.
4. Derive the total-variation bound from an L² density estimate.
5. Compute the spectral gap of the complete graph with off-diagonal rate r.
6. Compute the spectral gap for the two-state chain and compare it with both exit rates.
7. Prove that detailed balance makes \(D^{1/2}QD^{-1/2}\) symmetric.
8. Explain why the zero eigenvalue must be excluded from the gap.
9. Identify which part of the argument fails if π has zero mass at a state.
10. Formulate the abstract self-adjoint contraction theorem needed by the Poincaré route.

## Summary

For a reversible finite-state generator, detailed balance makes Q self-adjoint in the π-weighted inner product. Its Dirichlet form is nonnegative, and a Poincaré inequality with constant γ forces mean-zero observables to decay at least as e^{-γt} in L². Reversibility transfers that decay to densities, and Cauchy–Schwarz yields a total-variation mixing bound. Formalization can use either a weighted inner-product argument or a similarity transform to a symmetric matrix.

## Further reading

- [Mathlib: Spectral theory of Hermitian matrices](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html)
- [Mathlib: Symmetric matrices](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Symmetric.html)
- [Mathlib: Matrix exponential](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/MatrixExponential.html)
- Chapter 48 for total variation and discrete-time contraction.
- Chapters 45 and 55–59 for reversibility, generators, and continuous-time semigroups.
