# Chapter 70 — Tilted Generators and Large Deviations

> **Audience.** This chapter assumes finite-state semigroups, Feynman–Kac operators, spectral theory, and the empirical-measure viewpoint from earlier probability chapters. It develops the finite-matrix method for long-time fluctuations of additive observables.

An ergodic finite Markov chain spends a predictable fraction of a long run in each state, but finite runs fluctuate. Large deviations quantify the exponential cost of atypical behavior. For continuous-time chains, the main tool is a tilted generator: adding a potential to the diagonal turns an exponential path weight into a matrix semigroup. The long-time logarithmic moment generating function is the dominant eigenvalue of that matrix.

This chapter derives the transform for occupation times and jump rewards, explains how a spectral limit becomes a rate function, and works through a two-state example. The algebraic finite-state core is suitable for Lean; the full large-deviation lower bound should be separated from it and stated with its required spectral regularity.

## Learning objectives

By the end of this chapter, you should be able to:

- derive the Feynman–Kac matrix for an integrated state potential;
- tilt off-diagonal rates for additive jump rewards;
- identify the scaled cumulant generating function as a dominant eigenvalue;
- obtain occupation-measure rate functions by convex duality;
- compute the occupation-time transform for a two-state chain;
- distinguish matrix identities from the probabilistic LDP theorem.

## 1. Occupation observables

Let X_t be an irreducible continuous-time Markov chain on finite S with row generator Q. For a state observable \(V:S\to\mathbb R\), define its accumulated occupation reward by
\[
  A_T=\int_0^T V(X_s)\,ds.
\]
The empirical occupation measure is
\[
  L_T(i)=\frac1T\int_0^T\mathbf1_{\{X_s=i\}}\,ds,
\]
so \(A_T/T=\sum_iL_T(i)V(i)\). The vector L_T lies in the probability simplex: each coordinate is nonnegative and the coordinates sum to one.

For initial distribution α, the Feynman–Kac formula gives
\[
  \mathbb E_\alpha[e^{A_T}]
    =\alpha e^{T(Q+\operatorname{diag}V)}\mathbf1.
\]
The tilted matrix \(Q_V=Q+\operatorname{diag}V\) is generally not a generator: its row sums are \(V(i)\), not zero. It is a positive-weight evolution operator, not a probability transition matrix. Confusing it with a conservative generator leads to incorrect stochasticity claims.

For a scalar tilt \(\theta\), replace V by \(\theta V\). The scaled cumulant generating function is
\[
  \Lambda_V(\theta)=\lim_{T\to\infty}\frac1T
       \log\mathbb E_\alpha[e^{\theta A_T}].
\]
For a finite irreducible chain, \(\Lambda_V(\theta)\) is the spectral abscissa of \(Q+\theta\operatorname{diag}V\), independent of the initial state. The matrix is a Metzler matrix: off-diagonal entries are nonnegative. Shifting it by a sufficiently large multiple of the identity gives a nonnegative irreducible matrix, so Perron–Frobenius theory supplies a simple real dominant eigenvalue and positive left and right eigenvectors.

## 2. Why the dominant eigenvalue controls growth

Suppose A is an irreducible Metzler matrix with dominant eigenvalue Λ and positive right eigenvector r and left eigenvector ℓ. The exponential \(e^{tA}\) preserves the positive cone. Its long-time growth in a positive direction is \(e^{t\Lambda}\), while components associated with smaller real parts are exponentially negligible. Since α and 1 are positive on the communicating state space, the scalar \(\alpha e^{tA}\mathbf1\) has the same exponential rate:
\[
  \lim_{t\to\infty}\frac1t\log(\alpha e^{tA}\mathbf1)=\Lambda.
\]
This justifies the spectral formula for the scaled cumulant generating function.

The positivity of the initial and terminal vectors matters. If the chain is reducible or the initial law is supported in a component that cannot reach the dominant class, the scalar growth rate may select a different block. Irreducibility removes that ambiguity. In a formal theorem, state positivity of α or a fixed state start and irreducibility of the off-diagonal graph.

There are two proof routes. For reversible Q, conjugating by the square root of the stationary weights transforms Q into a symmetric matrix; adding a diagonal potential preserves symmetry, so the largest eigenvalue follows from the finite-dimensional spectral theorem. For nonreversible Q, a Perron–Frobenius theorem for irreducible nonnegative matrices is needed after shifting by a scalar. The two routes should not be merged into a false claim that every real matrix has real eigenvalues.

### Derivatives of the dominant eigenvalue

When the dominant eigenvalue is simple, it varies differentiably with \(\theta\). Let rθ be a positive right eigenvector and ℓθ a positive left eigenvector of \(A_\theta=Q+\theta\operatorname{diag}V\), normalized so \(\ell_\theta r_\theta=1\). Differentiating \(A_\theta r_\theta=\Lambda(\theta)r_\theta\) and pairing with ℓθ cancels the derivative of r:
\[
  \Lambda'(\theta)=\ell_\theta
       \operatorname{diag}(V)r_\theta.
\]
At \(\theta=0\), choose r₀=1 and ℓ₀=π. Then \(\Lambda'(0)=\pi(V)\), recovering the stationary mean as the first derivative of the long-run cumulant function.

The second derivative at zero is the asymptotic variance rate of the integrated observable. Under stationarity and exponential mixing it can also be written as twice the integral of the time covariance. This connects spectral curvature to correlation decay and gives a quantitative interpretation of the second derivative. In a formal proof, differentiate the simple eigenpair equation only after proving eigenvalue simplicity; otherwise an arbitrary eigenbasis choice may not be differentiable.

## 3. Worked example: occupation time in a two-state chain

Let the chain jump \(0\to1\) at rate a and \(1\to0\) at rate b, both positive. Let V record occupation of state 0. The tilted matrix is
\[
  Q_\theta+\operatorname{diag}(\theta V)
   =\begin{pmatrix}-a+\theta&a\\b&-b\end{pmatrix}.
\]
Its eigenvalues solve
\[
  \lambda^2-(\theta-a-b)\lambda-b\theta=0.
\]
The dominant eigenvalue is
\[
  \Lambda(\theta)=\frac12\left(\theta-a-b+
     \sqrt{(\theta+b-a)^2+4ab}\right).
\]
At \(\theta=0\), \(\Lambda(0)=0\), as required because the exponential moment at zero tilt is 1. Its derivative is \(\Lambda'(0)=b/(a+b)\), the stationary probability of state 0. Its second derivative at zero gives the asymptotic variance rate of occupation time.

The occupation fraction \(L_T(0)\) satisfies a large-deviation principle with rate function
\[
  I(x)=\sup_{\theta\in\mathbb R}\{\theta x-\Lambda(\theta)\}
      =\bigl(\sqrt{a x}-\sqrt{b(1-x)}\bigr)^2,
      \qquad 0\leq x\leq1,
\]
and \(I(x)=+\infty\) outside [0,1]. The minimum is zero at \(x=b/(a+b)\), the stationary occupation fraction. At \(x=0\), the cost is b, corresponding to avoiding the transition from state 1 into state 0; at \(x=1\), the cost is a.

This example offers two independent formal checks. Compute the eigenvalue from the characteristic polynomial and verify its derivatives at zero. Then establish the explicit Legendre transform by solving the one-variable optimization problem. The rate function formula is a theorem about the long-time distribution, not merely a symbolic consequence of the matrix eigenvalue; keep those layers separate.

Near its minimizer (x_* = b/(a+b)), the rate function has quadratic behavior governed by the asymptotic variance: (I(x)\approx (x-x_*)^2/(2\Lambda''(0))) when Λ″(0)>0. This local expansion connects the central limit scale to the exponential tail scale. The exact rate function controls deviations of fixed size, while its curvature predicts the Gaussian approximation for small deviations. A formal proof can derive the curvature identity by twice differentiating the eigenvalue equation and comparing it with the Legendre relation.

## 4. Occupation-measure large deviations

For a potential \(W:S\to\mathbb R\), let Λ(W) be the dominant eigenvalue of \(Q+\operatorname{diag}W\). The finite-state occupation-measure rate function is the convex dual
\[
  I(\mu)=\sup_{W:S\to\mathbb R}
       \left\{\sum_i\mu(i)W(i)-\Lambda(W)\right\},
\]
for probability vectors \(\mu\). Since adding a constant c to W shifts Λ(W) by c, the expression is unchanged on the probability simplex. This shift invariance is a useful algebraic lemma and a good check on the definition.

The rate function is nonnegative and vanishes at the stationary law. Convexity follows because it is a supremum of affine functions of μ. Compactness of the finite simplex gives exponential tightness automatically. A complete LDP proof still needs a lower-bound argument; differentiability of Λ and exposed-point results can provide it, while a finite-state Donsker–Varadhan theorem gives a direct route. Do not infer the full lower bound from the moment-generating-function identity alone.

Convexity of the limiting cumulant function can be proved before any spectral calculation: for finite T, Hölder’s inequality makes \(T^{-1}\log\mathbb E[e^{\theta A_T}]\) convex in θ, and a pointwise finite limit preserves convexity. Since V is bounded on a finite state space, the moment generating function exists for every real θ. This yields a proper convex dual on the full real line and makes the optimizer interpretation precise. In Lean, this route may be simpler than differentiating eigenvalues merely to prove convexity.

Even without proving the full LDP, the transform gives exponential tail bounds. For \(\theta>0\), Markov’s inequality yields
\[
  \Pr_\alpha(A_T/T\geq x)
    \leq e^{-\theta Tx}\,\alpha e^{T(Q+\theta\operatorname{diag}V)}\mathbf1.
\]
Taking logarithms, dividing by T, and using the spectral limit gives an asymptotic upper exponent no larger than \(-\bigl(\theta x-\Lambda(\theta)\bigr)\). Optimizing over positive θ gives the Chernoff bound for the upper tail; negative tilts handle the lower tail. This application requires only the exponential-moment identity and eigenvalue asymptotic, not the LDP lower bound.

The occupation rate can also be expressed variationally using the generator. For reversible chains, a particularly elegant formula involves the Dirichlet form of the square root of the density of μ relative to π. For nonreversible chains, the corresponding variational expression is more subtle. This chapter uses convex duality because it follows directly from the tilted semigroup and makes the normalization transparent.

Convex duality also clarifies which tilts detect a chosen empirical value. At a differentiability point, if (x=\Lambda'(\theta)), then θ is a supporting slope and the Legendre supremum is attained there:
\[
  I(x)=\theta x-\Lambda(\theta).
\]
This saddle-point relation is useful for asymptotic estimates and for proving lower bounds at exposed points. If V takes values between (v_{\min}) and (v_{\max}), then (A_T/T) always lies in that interval, so the scalar rate is infinite outside it. At endpoints, the cost is controlled by how long the chain can remain in the extremal state set; differentiability alone does not remove the need to check boundary behavior.

The same logic applies to vector-valued rewards. The gradient (\nabla\Lambda(\theta)) gives the empirical mean selected by a tilt, and the rate is the multivariate convex conjugate. In Lean, define the conjugate as a supremum over a finite-dimensional real vector space and prove basic facts—constant-shift invariance, nonnegativity at the stationary mean, and convexity—before attempting a full LDP theorem.

## 5. Additive jump rewards

Let each transition \(i\to j\) carry a reward g(i,j), and define
\[
  J_T=\sum_{0<s\leq T}g(X_{s-},X_s).
\]
The exponential moment of J_T is governed by a different tilted matrix. For i≠j set
\[
  Q_\theta^g(i,j)=q(i,j)e^{\theta g(i,j)},
  \qquad Q_\theta^g(i,i)=Q(i,i).
\]
The diagonal stays equal to the original negative exit rate; it is not reset to make the tilted rows sum to zero. Conditioning on the first jump or differentiating the Feynman–Kac evolution gives
\[
  \mathbb E_\alpha[e^{\theta J_T}]
    =\alpha e^{TQ_\theta^g}\mathbf1.
\]
At \(\theta=0\) this is the ordinary generator. For \(\theta\ne0\) the matrix is generally not conservative, because the path weight changes the mass of each trajectory.

Occupation rewards and jump rewards can be combined: add θV(i) to the diagonal and multiply off-diagonal rates by \(e^{\theta g(i,j)}\). The resulting spectral value controls joint cumulants and joint large deviations. Multiple parameters produce a vector-valued cumulant function and a multidimensional Legendre transform.

Because the chain has finitely many states and bounded exit rates, the number of jumps on a finite interval is dominated by a Poisson random variable after uniformization. Hence every exponential moment of a bounded jump reward exists at finite T. This justifies differentiating the finite-time moment generating function near zero and identifying its first derivative with the expected accumulated reward. The long-time spectral limit is a separate passage to infinity; keeping those two operations distinct avoids interchanging a derivative and a limit without a uniform bound.

## 6. Worked example: counting transitions

In the two-state chain, count every jump by assigning g(i,j)=1. The tilted matrix is
\[
  Q_\theta^g=\begin{pmatrix}-a&ae^\theta\\be^\theta&-b\end{pmatrix}.
\]
The dominant eigenvalue is
\[
  \Lambda_g(\theta)=\frac12\left(-a-b+
     \sqrt{(a-b)^2+4ab e^{2\theta}}\right).
\]
At zero its derivative is \(2ab/(a+b)\), which is the stationary mean jump rate: the chain is in state 0 with probability \(b/(a+b)\) and jumps out at rate a, or in state 1 with probability \(a/(a+b)\) and jumps out at rate b. Both contributions equal \(ab/(a+b)\).

This example shows why the diagonal convention matters. If one replaced the diagonal by minus the tilted outgoing sum, the resulting matrix would be a new generator and its exponential would preserve total mass. It would describe a changed chain, not the exponential weighting of the original path count.

## 7. Formalization strategy

The proof dependencies are:

```text
path reward ──> tilted finite matrix ──> Feynman–Kac semigroup identity
                                             │
                                             v
                                   dominant eigenvalue limit
                                             │
                                             v
                                  convex dual rate function
                                             │
                                             v
                                  large-deviation bounds
```

First prove the finite-time Feynman–Kac identity. For integrated rewards this is Chapter 59’s semigroup theorem; for jump rewards, prove a first-jump recursion or a generator perturbation lemma. Next establish the large-time spectral asymptotic. Finally invoke or prove the LDP lower and upper bounds. This order lets an application use the exact exponential-moment formula even when it does not need a full rate theorem.

Mathlib’s finite-dimensional spectral theorem is strongest for Hermitian matrices. A reversible tilted generator can be conjugated into that setting, while a nonreversible chain needs a Perron–Frobenius argument for a shifted nonnegative matrix. The custom bridge should identify the spectral abscissa of a Metzler matrix with the growth rate of its exponential. Do not call a generic eigenvalue maximum unless the theorem’s hypotheses ensure real eigenvalues and a positive eigenvector.

To build the nonnegative shift explicitly, choose c strictly larger than every exit rate minus the corresponding potential value. Then \(A+cI\) has nonnegative diagonal and the same off-diagonal support as Q. Irreducibility is retained, and the positive diagonal makes the shifted matrix primitive on a nontrivial communicating state space. Perron–Frobenius supplies its positive eigenvectors; subtracting c shifts the dominant eigenvalue back to that of A. A Lean interface can package this as a lemma for irreducible Metzler matrices, so reward-specific proofs never repeat the diagonal estimate.

## 8. Common failure modes

### The tilted matrix is forced to have row sums zero

Tilting changes path weights. The matrix is not a probability generator away from zero tilt.

### The diagonal is tilted for a jump reward

Keep the original exit-rate diagonal; only off-diagonal transitions receive the reward factor.

### A moment formula is mistaken for a full LDP

The spectral limit gives the scaled cumulant generating function. The lower bound needs a separate theorem or exposed-point argument.

### The initial distribution is ignored in a reducible chain

The dominant block may not be accessible from the initial support. Irreducibility avoids this issue.

### Reversibility is assumed for all models

The Feynman–Kac identity is general. Reversibility only supplies a convenient symmetric spectral route and special rate formulas.

## 9. Exercises

1. Prove the Feynman–Kac identity for an integrated potential on a two-state chain.
2. Derive the occupation-time eigenvalue Λ(θ) and check Λ'(0)=π(V).
3. Verify the two-state occupation rate function by Legendre transformation.
4. Show that adding a constant to V shifts Λ by that constant.
5. Derive the tilted matrix for a general jump reward g.
6. Explain why the diagonal of the jump-tilted matrix remains Q(i,i).
7. Compute the asymptotic jump count rate in the two-state model.
8. State the extra theorem needed to turn a differentiable cumulant function into an LDP lower bound.
9. Describe how reversibility transforms a tilted generator into a symmetric matrix.
10. Build a Lean structure for a finite-state reward and its associated tilted operator.

## Summary

Exponential path weights for finite continuous-time chains are encoded by tilted matrices. Integrated state rewards add a diagonal potential; jump rewards multiply off-diagonal rates while leaving the original exit diagonal in place. The dominant eigenvalue gives the scaled cumulant generating function, whose convex dual is the occupation or reward rate function under the appropriate finite-state large-deviation theorem. The key formalization boundary is between exact finite-time Feynman–Kac algebra, spectral asymptotics, and the LDP bounds.

## Further reading

- Chapters 59 and 68 for Feynman–Kac semigroups, killing, and finite spectral structure.
- [Mathlib’s finite Hermitian matrix spectral theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html).
- [Mathlib’s finite-dimensional self-adjoint spectral theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Spectrum.html).
