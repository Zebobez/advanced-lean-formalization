# Chapter 86 — Spectral Asymptotics of Matrix-Geometric Tails

> **Audience.** This chapter assumes familiarity with Perron–Frobenius theory, eigenvectors, spectral radius, and matrix-geometric stationary distributions. It explains when the dominant eigenvalue of a rate matrix controls the large-level tail and what additional information its eigenvectors provide.

Chapter 85 derived exact tail probabilities from the matrix-geometric law. Exact formulas answer a threshold question when the rate matrix is available, but a modeler also wants to understand the tail at very large levels: what is its exponential decay rate, and which phases dominate congestion? Perron–Frobenius theory gives a concise answer when the nonnegative rate matrix is primitive.

The assumptions matter. Nonnegativity alone does not guarantee one asymptotic phase profile. Reducibility can hide the dominant class from the boundary vector, and periodicity can create oscillations among levels. This chapter states a clean primitive case, derives its constants, and shows how to keep the spectral theorem separate from the queueing algebra in Lean.

## Learning objectives

After this chapter, you should be able to:

- derive level and tail asymptotics from a primitive rate matrix;
- identify the asymptotic decay parameter and high-level phase distribution;
- explain why irreducibility without aperiodicity can produce periodic behavior;
- distinguish a useful asymptotic estimate from a certified finite-threshold bound;
- package Perron data as explicit hypotheses for a Lean theorem.

## 1. Exact matrix-geometric tails

Let the stationary level vectors have the form

\[
\pi_n=\pi_0R^n,\qquad n\geq0,
\tag{86.1}
\]

where \(R\) is a finite square nonnegative matrix with spectral radius less than one, and the probability vector is normalized. As in Chapter 85, the phase-resolved tail from level \(K\) onward is

\[
\tau_K=\sum_{n=K}^{\infty}\pi_n
=\pi_0R^K(I-R)^{-1},
\tag{86.2}
\]

so the scalar level tail is

\[
\mathbb P(L\geq K)=\pi_0R^K(I-R)^{-1}\mathbf1.
\tag{86.3}
\]

These identities are exact for every \(K\). Spectral analysis asks what happens to (86.2) and (86.3) as \(K\) grows. It is useful to first isolate the matrix power \(R^K\), because its dominant eigenspace controls the asymptotic direction of both formulas.

## 2. Perron data for a primitive rate matrix

A nonnegative matrix \(R\) is primitive if some positive integer power has all entries strictly positive. Assume \(R\) is primitive and \(\rho(R)=r\) with \(0<r<1\). Perron–Frobenius theory provides:

- a strictly positive right eigenvector \(v\) with \(Rv=rv\);
- a strictly positive left eigenvector \(u\) with \(uR=ru\);
- a simple eigenvalue \(r\), with every other eigenvalue having modulus strictly less than \(r\).

Treat \(u\) as a row vector and normalize the pair so that \(uv=1\). The power-convergence theorem then gives

\[
r^{-n}R^n\longrightarrow vu.
\tag{86.4}
\]

The right vector \(v\) describes how mass moves forward through phases as levels increase. The left vector \(u\) describes the phase profile seen in stationary mass at high levels. The normalization \(uv=1\) makes the rank-one matrix \(vu\) a projection: \((vu)^2=v(uv)u=vu\).

For a nonnegative boundary vector \(\pi_0\neq0\), strict positivity of \(v\) implies \(\pi_0v>0\). Multiplying (86.4) on the left by \(\pi_0\) yields

\[
r^{-n}\pi_n
=r^{-n}\pi_0R^n
\longrightarrow(\pi_0v)u.
\tag{86.5}
\]

Thus the stationary probability of any particular phase at level \(n\) is asymptotic to \(r^n\) times the corresponding component of \((\pi_0v)u\).

### Why primitivity is the clean hypothesis

If \(R\) is irreducible but periodic with period \(d>1\), it can have several eigenvalues on the spectral circle, such as \(r\exp(2\pi i j/d)\). Then \(r^{-n}R^n\) need not converge along all levels; subsequences in fixed residue classes modulo \(d\) may have distinct limits. If \(R\) is reducible, its dominant eigenvalue may belong to a class that \(\pi_0\) cannot reach, or there may be several competing dominant blocks.

These cases still admit more detailed spectral descriptions, but a single positive rank-one limit is no longer automatic. When applying the clean theorem, prove primitivity or state the stronger spectral-gap and nonzero-projection hypotheses directly.

## 3. Asymptotic tail constant and phase mix

Substitute (86.4) into the exact tail formula (86.2):

\[
r^{-K}\tau_K
=\pi_0(r^{-K}R^K)(I-R)^{-1}
\longrightarrow(\pi_0v)u(I-R)^{-1}.
\tag{86.6}
\]

Since \(uR=ru\), the left eigenvector is also a left eigenvector of the resolvent:

\[
u(I-R)^{-1}=\frac{1}{1-r}u.
\tag{86.7}
\]

To see this, multiply \(u(I-R)=(1-r)u\) on the right by the inverse. Combining (86.6) and (86.7),

\[
\tau_K\sim r^K\frac{\pi_0v}{1-r}\,u,
\tag{86.8}
\]

where vector asymptotics are coordinatewise, or equivalently in any norm on the finite-dimensional phase space. Summing over phases gives

\[
\mathbb P(L\geq K)
\sim C r^K,\qquad
C=\frac{(\pi_0v)(u\mathbf1)}{1-r}.
\tag{86.9}
\]

The constant \(C\) depends on the boundary distribution as well as the rate matrix. The exponential decay parameter \(r\) is a property of the dominant spectral mode, while the amplitude records how much stationary mass enters that mode.

Normalize the left Perron vector to obtain a probability row vector

\[
\widehat u=\frac{u}{u\mathbf1}.
\tag{86.10}
\]

Equation (86.5) shows that the phase distribution conditional on being at a high exact level converges to \(\widehat u\). Equation (86.8) gives the same limit when conditioning on being at or above a high threshold:

\[
\frac{\tau_K}{\tau_K\mathbf1}\longrightarrow\widehat u.
\tag{86.11}
\]

This is a useful qualitative conclusion: at high congestion, the phase profile stabilizes even though the level continues to grow. The limiting profile is generally not the unconditional phase marginal \(q=\pi_0(I-R)^{-1}\) from Chapter 85.

Dividing adjacent scalar tails in (86.9) gives

\[
\lim_{K\to\infty}
\frac{\mathbb P(L\geq K+1)}{\mathbb P(L\geq K)}
=r.
\tag{86.12}
\]

The ratio is an asymptotic statement. At moderate thresholds, the exact tail can have substantial contributions from subdominant eigenvalues.

## 4. Reading the rate of convergence

Let \(r_2\) be the largest modulus among eigenvalues other than \(r\). Under primitivity, \(r_2<r\). If \(R\) is diagonalizable, the correction in (86.4) is controlled by powers of \(r_2/r\). More precisely, the normalized error is bounded by a constant times \((r_2/r)^n\). If \(R\) has nontrivial Jordan blocks, polynomial factors in \(n\) may multiply the subdominant exponential terms.

This distinction matters in numerical work. A small gap between \(r\) and \(r_2\) means that the asymptotic phase profile may become accurate only at very large levels. Knowing only the Perron root is enough to predict the ultimate logarithmic decay rate, but not enough to guarantee that \(Cr^K\) is a tight approximation at a particular \(K\).

For an engineering threshold such as \(\mathbb P(L\geq K)\leq\varepsilon\), the asymptotic approximation suggests

\[
K\approx\frac{\log(\varepsilon/C)}{\log r}.
\tag{86.13}
\]

Because \(0<r<1\), the denominator is negative. The direction of the inequality reverses when dividing by \(\log r\). Equation (86.13) is a planning estimate; a final capacity guarantee should use the exact formula (86.3) or a rigorous upper bound.

The quantity \(-1/\log r\) is an asymptotic e-folding distance in levels: increasing the threshold by that many levels multiplies the leading tail approximation by about \(e^{-1}\). When \(r\) is near one, \(-\log r\) is close to \(1-r\), so the tail decays slowly and the required capacity can be large. This scale is descriptive rather than a replacement for the exact mean or tail calculations in Chapter 85.

### Sensitivity of the decay rate

Suppose the model depends smoothly on a parameter \(\theta\), such as a service rate, admission probability, or arrival intensity. Write the corresponding primitive rate matrix as \(R(\theta)\), with Perron root \(r(\theta)\). If \(r(\theta)\) remains a simple isolated eigenvalue and the left and right Perron vectors are differentiable and normalized by \(u(\theta)v(\theta)=1\), then differentiating \(Rv=rv\) and multiplying on the left by \(u\) cancels the terms involving \(v'\). The result is

\[
r'(\theta)=u(\theta)R'(\theta)v(\theta).
\tag{86.14}
\]

For a tail approximation \(\mathbb P_\theta(L\geq K)\approx C(\theta)r(\theta)^K\), logarithmic differentiation gives

\[
\frac{\partial}{\partial\theta}
\log\mathbb P_\theta(L\geq K)
\approx \frac{C'(\theta)}{C(\theta)}
+K\frac{r'(\theta)}{r(\theta)}.
\tag{86.15}
\]

At high thresholds, the term multiplied by \(K\) can dominate. A small change to the Perron root can therefore have a large relative effect on rare congestion probabilities. This conclusion is local and asymptotic: a finite-threshold sensitivity should be derived from the exact tail formula, and uniform control of the spectral gap is needed before differentiating a limit.

## 5. Worked example: a positive two-phase rate matrix

Consider

\[
R=\begin{pmatrix}
0.3&0.1\\
0.2&0.4
\end{pmatrix}.
\tag{86.16}
\]

Every entry is positive, so \(R\) is primitive. Its characteristic polynomial is

\[
\lambda^2-0.7\lambda+0.1
=(\lambda-0.5)(\lambda-0.2).
\]

The Perron root is \(r=1/2\). A right eigenvector is \(v=(1,2)^{\mathsf T}\), and a left eigenvector is \(u=(1/3,1/3)\), satisfying \(uv=1\).

Choose the nonnegative row vector \(\pi_0=(1/2,1/18)\). This gives a normalized geometric probability law because

\[
(I-R)^{-1}\mathbf1
=\begin{pmatrix}7/4\\9/4\end{pmatrix},
\qquad
\pi_0(I-R)^{-1}\mathbf1
=\frac12\frac74+\frac1{18}\frac94=1.
\]

This example isolates the spectral calculation and does not claim a particular queue boundary equation. The projection constant is

\[
\pi_0v=\frac12+\frac{2}{18}=\frac{11}{18}.
\]

The level-vector asymptotic is therefore

\[
\pi_n\sim \left(\frac12\right)^n
\left(\frac{11}{54},\frac{11}{54}\right).
\tag{86.17}
\]

The asymptotic phase mix is \((1/2,1/2)\). Since \(u\mathbf1=2/3\), the scalar tail constant is

\[
C=\frac{(11/18)(2/3)}{1-1/2}=\frac{22}{27},
\]

and hence \(\mathbb P(L\geq K)\sim(22/27)(1/2)^K\). The second eigenvalue is \(0.2\), so the relative correction decays at a rate proportional to \((0.2/0.5)^K=(0.4)^K\). This spectral gap explains how quickly the phase mixture approaches its limiting profile.

### 5.1 An executable Perron-data certificate

The two-phase example has a positive rate matrix with exact rational Perron data: right eigenvector column v = (1, 2), left eigenvector row u = (1/3, 1/3), Perron root 1/2, and second eigenvalue 1/5. The code verifies these eigenvector equations, the normalization u v = 1, the rank-one projection identity, and the exact resolvent calculation used for the boundary normalization. It also checks the tail amplitude 22/27 and each coordinate of the limiting level-vector amplitude. These finite certificates provide the numerical input for the asymptotic theorem; they do not prove the general Perron power-convergence result.

```lean
abbrev SpectralMatrix := Matrix (Fin 2) (Fin 2) ℚ

def spectralR : SpectralMatrix := !![3 / 10, 1 / 10; 1 / 5, 2 / 5]
def spectralResolvent : SpectralMatrix := !![3 / 2, 1 / 4; 1 / 2, 7 / 4]

def spectralRight (i : Fin 2) : ℚ := if i = 0 then 1 else 2
def spectralLeft (_i : Fin 2) : ℚ := 1 / 3
def spectralSecondRight (i : Fin 2) : ℚ := if i = 0 then 1 else -1
def spectralBoundary (i : Fin 2) : ℚ := if i = 0 then 1 / 2 else 1 / 18
def spectralOnes (_i : Fin 2) : ℚ := 1

def spectralMatVec (A : SpectralMatrix) (v : Fin 2 → ℚ) (i : Fin 2) : ℚ :=
  ∑ j : Fin 2, A i j * v j

def spectralRowVec (u : Fin 2 → ℚ) (A : SpectralMatrix) (j : Fin 2) : ℚ :=
  ∑ i : Fin 2, u i * A i j

def spectralDot (u v : Fin 2 → ℚ) : ℚ :=
  ∑ i : Fin 2, u i * v i

def spectralProjection (i j : Fin 2) : ℚ := spectralRight i * spectralLeft j

def spectralCharacteristic (x : ℚ) : ℚ :=
  (3 / 10 - x) * (2 / 5 - x) - 1 / 50

theorem spectralR_positive : ∀ i j : Fin 2, 0 < spectralR i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [spectralR]

theorem spectral_right_eigenvector :
    ∀ i : Fin 2,
      spectralMatVec spectralR spectralRight i = (1 / 2 : ℚ) * spectralRight i := by
  intro i
  fin_cases i <;> norm_num [spectralMatVec, spectralR, spectralRight]

theorem spectral_left_eigenvector :
    ∀ j : Fin 2,
      spectralRowVec spectralLeft spectralR j = (1 / 2 : ℚ) * spectralLeft j := by
  intro j
  fin_cases j <;> norm_num [spectralRowVec, spectralLeft, spectralR]

theorem spectral_perron_pair_normalized :
    spectralDot spectralLeft spectralRight = 1 := by
  norm_num [spectralDot, spectralLeft, spectralRight]

theorem spectral_second_eigenvector :
    ∀ i : Fin 2,
      spectralMatVec spectralR spectralSecondRight i =
        (1 / 5 : ℚ) * spectralSecondRight i := by
  intro i
  fin_cases i <;> norm_num [spectralMatVec, spectralR, spectralSecondRight]

theorem spectral_characteristic_factorization (x : ℚ) :
    spectralCharacteristic x = (x - 1 / 2) * (x - 1 / 5) := by
  unfold spectralCharacteristic
  ring

theorem spectral_projection_idempotent (i j : Fin 2) :
    ∑ k : Fin 2, spectralProjection i k * spectralProjection k j =
      spectralProjection i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [spectralProjection, spectralRight, spectralLeft]

theorem spectralResolvent_left_inverse :
    (1 - spectralR) * spectralResolvent = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spectralR, spectralResolvent, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.one_apply]

theorem spectralResolvent_right_inverse :
    spectralResolvent * (1 - spectralR) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spectralR, spectralResolvent, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.one_apply]

theorem spectralResolvent_apply_ones :
    ∀ i : Fin 2, spectralMatVec spectralResolvent spectralOnes i =
      (if i = 0 then 7 / 4 else 9 / 4) := by
  intro i
  fin_cases i <;>
    norm_num [spectralMatVec, spectralResolvent, spectralOnes]

theorem spectralBoundary_normalized :
    spectralDot spectralBoundary
      (fun i => if i = 0 then 7 / 4 else 9 / 4) = 1 := by
  norm_num [spectralDot, spectralBoundary]

theorem spectralBoundary_dot_right :
    spectralDot spectralBoundary spectralRight = 11 / 18 := by
  norm_num [spectralDot, spectralBoundary, spectralRight]

theorem spectralLeft_mass : (∑ i : Fin 2, spectralLeft i) = 2 / 3 := by
  norm_num [spectralLeft]

theorem spectralTailConstant :
    (spectralDot spectralBoundary spectralRight) *
      (∑ i : Fin 2, spectralLeft i) / (1 - 1 / 2) = 22 / 27 := by
  norm_num [spectralDot, spectralBoundary, spectralRight, spectralLeft]

theorem spectralAsymptoticAmplitude (i : Fin 2) :
    spectralDot spectralBoundary spectralRight * spectralLeft i = 11 / 54 := by
  fin_cases i <;> norm_num [spectralDot, spectralBoundary, spectralRight, spectralLeft]
```

## 6. Spectral analysis and Lean interfaces

### 6.1 Package the Perron hypotheses

An asymptotic theorem should not repeatedly expand the definition of primitivity or spectral radius. Introduce a structure that records:

- a finite phase type and a nonnegative square matrix \(R\);
- a real number \(r\) with \(0<r<1\);
- left and right eigenvector equations \(uR=ru\) and \(Rv=rv\);
- positivity of the eigenvectors and normalization \(uv=1\);
- convergence of \(r^{-n}R^n\) to the outer product \(vu\).

There are two reasonable proof boundaries. One can prove the Perron power-convergence theorem from Mathlib's finite-dimensional spectral theory and a primitivity hypothesis, or take that convergence as an explicit field in a reusable Perron-data structure. The latter keeps queueing asymptotics independent of the details of a substantial linear-algebra proof.

In Lean, take care with the scalar field of the spectrum. A real matrix can have nonreal eigenvalues, so a proof that every non-Perron eigenvalue has smaller modulus naturally refers to the complexified matrix. The convergence result itself can be stated in a real matrix norm. Packaging the real Perron root, its eigenvectors, and the power limit avoids silently identifying a real spectral-radius value with an eigenvalue without a theorem.

For instance, a Lean-shaped specification could include the limit directly:

~~~lean
structure PerronData (Phase : Type) [Fintype Phase] where
  R : Matrix Phase Phase ℝ
  rho : ℝ
  left : Phase → ℝ
  right : Phase → ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  left_eigen : rowMul left R = rho • left
  right_eigen : R.mulVec right = rho • right
  normalize : rowMul left right = 1
  power_limit :
    Tendsto (fun n : ℕ => rho ^ (-(n : ℤ)) • R ^ n)
      atTop (nhds (outerProduct right left))
~~~

This illustrates the contract rather than a checked Mathlib declaration; matrix row multiplication, scalar action, and real powers may need a library-specific encoding. In implementation, it can be simpler to express \(r^{-n}\) as \((r^n)^{-1}\), using the explicit hypothesis \(r>0\).

### 6.2 Derive the level limit by continuous operations

Once the matrix-power limit is available, (86.5) follows by applying the continuous linear map that left-multiplies a matrix by \(\pi_0\). A Lean proof should expose that map rather than unfold every matrix entry:

1. rewrite \(\pi_n\) as \(\pi_0R^n\);
2. factor out the positive scalar \(r^{-n}\);
3. apply the matrix power limit;
4. simplify \(\pi_0(vu)=(\pi_0v)u\).

This proof pattern is reusable for any row vector placed at the boundary. The scalar asymptotic follows by continuous multiplication by \((I-R)^{-1}\mathbf1\), then by the eigenvector identity (86.7).

### 6.3 Keep the limit theorem separate from exact tails

The exact tail theorem (86.2) uses only a convergent geometric matrix series. The asymptotic theorem adds Perron data and a limit. Keep them as separate theorems:

- exact tail vector from summability of matrix powers;
- power convergence from primitivity or a stated spectral-gap condition;
- tail asymptotic from the first two results;
- normalized high-level phase limit after proving that the scalar denominator has a positive limit.

This layering makes the exact formula useful even in reducible or periodic cases. It also makes a failed spectral assumption local: the user can still compute exact tails without pretending that one phase profile dominates.

### 6.4 Handle asymptotic equivalence explicitly

The notation \(a_K\sim b_K\) usually means \(a_K/b_K\to1\) with an eventual nonzero denominator. For vectors, some libraries define asymptotic equivalence only for scalar functions. A robust proof can instead establish a norm limit such as

\[
r^{-K}\tau_K\longrightarrow\frac{\pi_0v}{1-r}u,
\]

then derive each coordinate limit. For the scalar tail, prove convergence after multiplying by \(\mathbf1\). To obtain the adjacent-tail ratio, also establish a positive limiting constant, which follows here from \(\pi_0v>0\) and \(u\mathbf1>0\).

Avoid rewriting a vector limit as a componentwise ratio without proving each limiting component is positive. The left Perron vector is strictly positive under primitivity, so that positivity is available in this case.

## 7. Common failure modes

1. **Using the spectral radius without a spectral gap.** A dominant eigenvalue may not control a single limit if other eigenvalues share its modulus.
2. **Assuming irreducible means primitive.** Periodicity is a separate condition.
3. **Reversing left and right eigenvectors.** With row stationary vectors, the asymptotic row profile is the left Perron vector.
4. **Forgetting the boundary projection.** The amplitude contains \(\pi_0v\); it is not determined by \(R\) alone.
5. **Calling \(r^K\) the whole tail.** The finite-threshold tail also has the constant and subdominant corrections.
6. **Ignoring reducibility.** A dominant block inaccessible from \(\pi_0\) may not contribute to the observed tail.
7. **Treating an asymptotic approximation as a certificate.** A limit does not give a finite-\(K\) inequality without an explicit error bound.
8. **Normalizing the Perron pair inconsistently.** Rescaling \(u\) and \(v\) changes separate factors but not \(vu\); preserve \(uv=1\) in formulas.
9. **Discarding complex eigenvalues in the proof.** The matrix is real and nonnegative, but subdominant eigenvalues can be complex.
10. **Conflating exact level and tail phase profiles.** Their limits agree in the primitive case, but their finite-level vectors differ.

## 8. Exercises

1. Starting from (86.4), derive (86.5) and the vector tail limit (86.6).
2. Prove the resolvent identity (86.7) from \(uR=ru\).
3. Show that (86.9) follows from (86.8), and derive the adjacent-tail ratio (86.12).
4. For the matrix in (86.16), compute both eigenvalues and verify the left and right Perron vectors and their normalization.
5. Normalize \(\pi_0=(1/2,1/18)\) directly and verify the scalar tail constant.
6. Construct a two-phase irreducible but periodic nonnegative matrix and show why its normalized powers do not converge along all integers.
7. Give a reducible matrix whose largest-eigenvalue block is not reachable from a chosen boundary row. Explain why the boundary projection matters.
8. Derive the logarithmic threshold estimate (86.13) and explain why it is not a finite-threshold guarantee.
9. State a Lean theorem for the exact tail limit assuming matrix power convergence as a hypothesis, then a separate theorem deriving that hypothesis from Perron–Frobenius theory.
10. Compare the limiting high-level phase profile \(\widehat u\) with the unconditional phase marginal \(q=\pi_0(I-R)^{-1}\). Give a model in which they differ.

## 9. Summary

For a primitive nonnegative rate matrix with Perron root \(r\in(0,1)\), matrix powers satisfy \(r^{-n}R^n\to vu\), where \(v\) and \(u\) are normalized right and left Perron vectors. The stationary level vectors then satisfy \(\pi_n\sim r^n(\pi_0v)u\), and the tail satisfies \(\mathbb P(L\geq K)\sim Cr^K\), with \(C=(\pi_0v)(u\mathbf1)/(1-r)\). The normalized left Perron vector is the limiting phase mix at high levels.

Primitivity gives a clean limit; reducibility and periodicity require more detailed analysis. In Lean, keep the exact matrix-geometric tail theorem independent from the Perron convergence theorem, and derive asymptotics by applying continuous linear operations to the packaged matrix limit.

### Further reading

- M. F. Neuts and Y. Takahashi, [“Asymptotic behavior of the stationary distributions in the GI/PH/c queue with heterogeneous servers”](https://doi.org/10.1007/BF01025867), *Probability Theory and Related Fields* 57 (1981), 441–452. This work studies asymptotic stationary behavior in a phase-structured queueing model.
- M. F. Neuts, [“The caudal characteristic curve of queues”](https://doi.org/10.2307/1427244), *Advances in Applied Probability* 18 (1986), 221–254. This paper studies geometric decay parameters for stationary queue tails.
