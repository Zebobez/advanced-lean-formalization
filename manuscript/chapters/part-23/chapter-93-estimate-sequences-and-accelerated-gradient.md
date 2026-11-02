# Chapter 93 — Estimate Sequences and Accelerated Gradient

> **Audience.** This chapter assumes familiarity with smooth convex optimization and the descent lemma from Chapter 91. It studies the proof idea behind accelerated gradient methods: an auxiliary sequence of model functions whose weights shrink quadratically.

The basic gradient method turns smoothness into a decrease inequality and obtains an \(O(1/k)\) objective-gap rate. Acceleration improves this to \(O(1/k^2)\) for smooth convex objectives. The gain does not come from applying the same descent argument more forcefully. Momentum makes the objective values nonmonotone, so a proof that sums only objective decrease cannot explain the rate.

Estimate sequences provide a different invariant. They track auxiliary functions related to the objective by a weighted domination inequality, while the algorithm keeps its current value below the minimum of the auxiliary model. When the weights shrink like \(1/k^2\), the objective gap inherits that rate. This chapter develops the invariant, connects it to a standard accelerated recurrence, and explains how a proof assistant can represent the changing models without burying the argument in index arithmetic.

## Learning objectives

After this chapter, you should be able to:

- state an estimate-sequence bound and derive an objective-gap estimate from it;
- describe the accelerated gradient recurrence and its scalar weight update;
- explain why acceleration can have nonmonotone objective values;
- distinguish an accelerated rate theorem from a claim about every intermediate step;
- structure a Lean proof around model bounds, scalar recurrences, and an invariant;
- recognize how strong convexity changes momentum parameters and convergence rates.

## 1. Why the gradient-descent proof does not accelerate itself

For an \(L\)-smooth convex function, Chapter 91 proves

\[
f(x_k)-f_*\le\frac{L\|x_0-x_*\|^2}{2k}.
\tag{93.1}
\]

The proof uses the squared distance to an optimizer as a potential. Each gradient step decreases that distance by an amount proportional to the current function gap; summing telescopes the potential. This argument is already efficient for the update it analyzes, but it does not produce a quadratic rate.

Momentum introduces a second sequence. The method takes a gradient step at an extrapolated point \(y_k\), not necessarily at the current point \(x_k\). Consequently, the descent lemma controls \(f(x_{k+1})\) relative to \(f(y_k)\); it does not guarantee \(f(x_{k+1})\le f(x_k)\). A proof that silently assumes monotonicity will fail on simple quadratic examples.

The formal proof should therefore expose a different invariant. Rather than asking that every objective value decrease, it bounds a weighted combination of the current objective gap and an auxiliary model. The model carries information from the starting point and from the gradients seen so far.

## 2. Estimate sequences turn a model bound into a rate

Let \(f:E\to\mathbb R\) be convex and suppose it has a minimizer \(x_*\), with \(f_*=f(x_*)\). Choose an initial model \(\phi_0:E\to\mathbb R\). At iteration \(k\), suppose we have:

1. a weight \(\lambda_k\in[0,1]\);
2. a model \(\phi_k:E\to\mathbb R\) satisfying

\[
\phi_k(x)\le(1-\lambda_k)f(x)+\lambda_k\phi_0(x)
\qquad(x\in E);
\tag{93.2}
\]

3. an iterate \(x_k\) whose objective is bounded by the infimum of that model:

\[
f(x_k)\le\inf_{x\in E}\phi_k(x).
\tag{93.3}
\]

Then evaluate (93.2) at \(x_*\). Since an infimum is no larger than any particular value,

\[
f(x_k)\le\inf_x\phi_k(x)\le\phi_k(x_*)
\le(1-\lambda_k)f_*+\lambda_k\phi_0(x_*).
\]

Subtracting \(f_*\) gives the estimate-sequence bound

\[
f(x_k)-f_*
\le\lambda_k\bigl(\phi_0(x_*)-f_*\bigr).
\tag{93.4}
\]

This short argument is the reward for maintaining the more elaborate invariant. The optimization algorithm's work is to update \(\phi_k\) and \(x_k\) so that (93.2) and (93.3) continue to hold. The rate then follows from the scalar decay of \(\lambda_k\).

For an \(L\)-smooth objective, use the initial quadratic model

\[
\phi_0(x)=f(x_0)+\frac L2\|x-x_0\|^2.
\tag{93.5}
\]

At a differentiable unconstrained minimizer, \(\nabla f(x_*)=0\). The descent lemma applied from \(x_*\) to \(x_0\) yields \(f(x_0)-f_*\le(L/2)\|x_0-x_*\|^2\). Therefore

\[
\phi_0(x_*)-f_*
=f(x_0)-f_*+\frac L2\|x_*-x_0\|^2
\le L\|x_0-x_*\|^2.
\tag{93.6}
\]

If \(\lambda_k\) decays quadratically, (93.4) and (93.6) give an \(O(1/k^2)\) objective-gap rate. The constant depends on the normalization of the estimate sequence; the essential formal invariant is the inequality, not a particular choice of names for its weights.

### 2.1 A scalar model calculation

Take \(f(x)=\tfrac L2x^2\), \(x_0=1\), and \(x_*=0\). Then \(f_*=0\), and (93.5) gives

\[
\phi_0(x)=\frac L2+\frac L2(x-1)^2.
\]

At the minimizer, \(\phi_0(0)=L\), so (93.4) reads \(f(x_k)\le L\lambda_k\). If a model update proves \(\lambda_k\le c/(k+1)^2\), the quadratic example immediately inherits the bound \(f(x_k)\le cL/(k+1)^2\). Notice what has and has not been proved: the scalar estimate is immediate, but it depends on the algorithm-specific proof that the iterate is below the model infimum.

This separation is useful in formalization. The final rate theorem should not know how the estimate model was built. It consumes the two inequalities (93.2)–(93.3), then performs a short order argument.

### 2.2 Updating the model

Convexity supplies a global linear lower model at any point \(y\):

\[
\ell_y(x)=f(y)+\langle\nabla f(y),x-y\rangle\le f(x).
\]

Given a weight \(\alpha_{k+1}\in[0,1]\), one can mix the old model with this linearization:

\[
\phi_{k+1}(x)=(1-\alpha_{k+1})\phi_k(x)
+\alpha_{k+1}\ell_{y_k}(x).
\]

If \(\phi_k(x)\le(1-\lambda_k)f(x)+\lambda_k\phi_0(x)\), substitution and \(\ell_{y_k}(x)\le f(x)\) give the same form at the next step with

\[
\lambda_{k+1}=(1-\alpha_{k+1})\lambda_k.
\]

Thus a simple convex combination preserves the model bound. A constant \(\alpha\) would make \(\lambda_k\) decay geometrically, but the iterate-below-model obligation (93.3) also has to be preserved, and the associated algorithm cannot use arbitrary mixing weights. The accelerated schedule balances both obligations; its weights are chosen so the quadratic model minimizer, gradient step, and extrapolation all fit together.

When \(\phi_k\) is quadratic, adding a linearization leaves it quadratic, so its minimizer can be represented by a point and a scalar coefficient rather than a general function. This is one reason estimate sequences admit a compact formal representation. The Lean proof can store the quadratic's center and curvature and prove that the symbolic model update corresponds to the function-level recurrence.

## 3. The accelerated gradient recurrence

For a differentiable convex function with \(L\)-Lipschitz gradient on a real Hilbert space, a common accelerated recurrence is

\[
x_0=y_0,\qquad t_0=1,
\]

\[
x_{k+1}=y_k-\frac1L\nabla f(y_k),
\tag{93.7}
\]

\[
t_{k+1}=\frac{1+\sqrt{1+4t_k^2}}2,
\tag{93.8}
\]

\[
y_{k+1}=x_{k+1}
+\frac{t_k-1}{t_{k+1}}(x_{k+1}-x_k).
\tag{93.9}
\]

The variable \(y_k\) is the extrapolated point. The coefficient in (93.9) is determined by the scalar recurrence (93.8), which satisfies

\[
t_{k+1}^2-t_{k+1}=t_k^2.
\tag{93.10}
\]

This identity is the algebraic hinge of the accelerated proof. It makes the model weights fit the change in the momentum term. Also, \(t_k\ge1+k/2\): the recurrence gives \(t_{k+1}\ge t_k+1/2\), so a simple induction establishes the lower bound. Thus the reciprocal square of the weight is \(O(1/k^2)\).

For this recurrence, the estimate-sequence analysis gives the standard bound

\[
f(x_k)-f_*
\le\frac{2L\|x_0-x_*\|^2}{(k+1)^2}
\qquad(k\ge1).
\tag{93.11}
\]

The \(1/k^2\) rate is for the sequence \(x_k\) and the function values specified by this algorithm. It is not a statement that \(f(x_{k+1})\le f(x_k)\) at every step. Nesterov's original accelerated method established this rate for smooth convex optimization; the reference at the end of the chapter gives the original publication record.

### 3.1 What the invariant must remember

The update has two coupled effects:

- a gradient step uses the descent lemma at \(y_k\);
- an extrapolation moves \(y_{k+1}\) beyond the most recent point.

The auxiliary model absorbs the extrapolation. If the proof stores only \(x_k\) and its objective gap, the momentum term appears as an uncontrolled cross term. The estimate sequence stores enough history to complete the square and cancel that term using (93.10).

Different presentations package this information differently: some store a model function \(\phi_k\), some store a weighted average and a potential, and some use an energy inequality with an auxiliary vector. These can encode the same mathematical mechanism. For a Lean library, choose the representation that gives the cleanest one-step preservation lemma; do not force an exact transcription of a paper's notation when a simpler equivalent invariant proves the needed rate.

### 3.2 Accelerating a composite objective

Chapter 92's proximal step fits the same extrapolation pattern. For \(F=f+g\), where \(f\) is convex with \(L\)-Lipschitz gradient and \(g\) is proper lower semicontinuous convex, replace (93.7) by

\[
x_{k+1}=\operatorname{prox}_{g/L}
\left(y_k-\frac1L\nabla f(y_k)\right).
\]

Keep the scalar update (93.8) and the momentum formula (93.9). The proximal minimization handles \(g\) exactly; the estimate-sequence argument uses the smooth upper model for \(f\) and the convex lower model for \(g\). Under these hypotheses and assuming a minimizer exists, the same order of rate holds for the composite gap \(F(x_k)-F_*\). Taking \(g\) to be the indicator of a closed convex set recovers accelerated projected gradient.

This is where the interface from Chapter 92 pays off. The acceleration proof does not need to know whether the proximal map arose from an \(\ell^1\) penalty, a constraint indicator, or another convex term. It consumes the proximal three-point inequality. A formal library can therefore reuse the proximal optimality theorem and change only the estimate-sequence layer.

## 4. Strong convexity and the momentum scale

For a \(\mu\)-strongly convex, \(L\)-smooth objective, accelerated methods can achieve a geometric rate whose iteration scale depends on \(\sqrt{L/\mu}\), improving on the \({L}/{\mu}\) scale of ordinary gradient descent. A standard constant-momentum choice is

\[
\beta=\frac{\sqrt L-\sqrt\mu}{\sqrt L+\sqrt\mu},
\qquad 0<\mu\le L.
\tag{93.12}
\]

The corresponding form extrapolates by \(y_k=x_k+\beta(x_k-x_{k-1})\) and takes a gradient step from \(y_k\). A suitable potential gives a contraction factor governed by \(1-\sqrt{\mu/L}\). Exact constants and indexing depend on the strongly convex variant, so keep the theorem tied to the recurrence actually formalized.

### 4.1 A two-eigenvalue quadratic

Consider

\[
f(u,v)=\frac12(\mu u^2+L v^2)
\qquad(0<\mu\le L).
\tag{93.13}
\]

For the constant-momentum recurrence, each eigendirection evolves independently. Along an eigenvalue \(a\), the scalar error satisfies

\[
e_{k+1}=\left(1-\frac aL\right)
\bigl((1+\beta)e_k-\beta e_{k-1}\bigr).
\tag{93.14}
\]

For the flat direction \(a=\mu\), substitute \(\beta\) from (93.12) and set \(q=\sqrt{\mu/L}\). The characteristic polynomial becomes

\[
r^2-2(1-q)r+(1-q)^2=(r-(1-q))^2.
\tag{93.15}
\]

The slow mode therefore has a repeated root at \(1-\sqrt{\mu/L}\). The steep direction has \(a=L\), so its next error is zero regardless of the previous momentum. The quadratic makes the role of the condition number visible: acceleration targets the slow curvature scale by using a square root in the momentum parameter.

This calculation is an eigenmode explanation, not the full global proof. For a general smooth strongly convex function, there is no fixed Hessian basis in which all iterations decouple. The proof must use a global potential or an estimate sequence that controls all directions at once.

## 5. Lean proof architecture

### 5.1 Make the estimate invariant explicit

A compact model predicate can state the pointwise inequality:

~~~lean
def IsEstimateModel (f phi0 phi : E → ℝ) (lam : ℝ) : Prop :=
  0 ≤ lam ∧ lam ≤ 1 ∧
    ∀ x, phi x ≤ (1 - lam) * f x + lam * phi0 x
~~~

The rate proof also needs a certificate that the current iterate lies below the model's infimum. Whether this is represented with an infimum, a minimizer witness, or a lower-bound property depends on the model's coercivity and existence theorem. Keep those details in a separate structure so the short estimate (93.4) is independent of the model-update mechanism.

For a recursively built model, the induction step has three obligations:

1. preserve the weighted upper bound for every point;
2. prove the new iterate has objective at most the model infimum;
3. update the scalar weight and establish its algebraic identity.

The first two are analytic; the third is real arithmetic. Splitting them prevents a proof from asking nonlinear arithmetic automation to discover a vector-valued invariant.

### 5.2 Prove the scalar schedule separately

The update (93.8) contains a square root. Define its scalar properties once:

- positivity of \(t_k\);
- the identity (93.10);
- a lower bound linear in \(k\);
- the resulting upper bound on the reciprocal square.

In Lean, prove the square-root identity by isolating the defining equation and using nonnegativity, then use the recurrence in a natural-number induction. Avoid rewriting square roots throughout the main gradient proof. The vector analysis should consume only the scalar lemmas about \(t_k\) and the momentum coefficient.

### 5.3 Separate the accelerated step from the whole algorithm

Prove a single-step lemma that takes \(x_k,y_k,t_k\), the smoothness and convexity hypotheses, and the current model invariant, then returns the next model invariant. Define the infinite sequence only after that theorem is stable. For finite-horizon results, a recursive function on \(\mathbb N\) or a finite list can then reuse the one-step theorem by induction.

Because the iterates need not have monotone objective values, do not add a false invariant such as \(f(x_{k+1})\le f(x_k)\). State the terminal bound at index \(N\), or prove a bound on a specifically defined weighted average if the algorithm variant returns one.

### 5.4 Treat constants and indexing as part of the theorem

The exact numerator and denominator in (93.11) depend on initialization and whether the first update is called iteration zero or one. Store the recurrence and the theorem's index convention together. A proof may be mathematically correct asymptotically but still wrong by a shift in the finite statement.

For library design, it is useful to separate:

- an asymptotic theorem that states \(O(1/k^2)\);
- an explicit finite-\(k\) inequality such as (93.11);
- a corollary converted into a requested iteration count for a target tolerance.

The finite inequality is the reusable theorem. Big-O notation is appropriate in exposition, but it should not replace the explicit quantitative statement in a Lean declaration.

## 6. Common failure modes

1. **Assuming accelerated objective values decrease every iteration.** Momentum can make them rise temporarily.
2. **Applying the descent lemma at the wrong point.** The gradient is evaluated at \(y_k\), so smoothness compares \(x_{k+1}\) with \(y_k\).
3. **Ignoring the auxiliary invariant.** The \(1/k^2\) rate does not follow from the ordinary gradient-descent telescope alone.
4. **Treating the momentum coefficient as arbitrary.** The scalar recurrence is matched to the model weights.
5. **Proving only the weight identity.** The identity controls one cross term; it does not establish the estimate-sequence invariant by itself.
6. **Confusing an asymptotic rate with a finite bound.** State constants and index shifts explicitly.
7. **Using a minimizer without an existence hypothesis.** The estimate-sequence comparison assumes \(x_*\) exists, unless a separate infimum-based version is proved.
8. **Transferring the smooth rate to a nonsmooth objective.** Composite acceleration needs a proximal step and its own model argument, as in Chapter 92.
9. **Generalizing the typeclass context too early.** The proof needs real order, an inner product, and a norm; abstract only after the invariant is clear.
10. **Comparing different variants by their names alone.** Verify the actual update and initialization before importing a theorem.

## 7. Exercises

1. Prove the estimate-sequence implication (93.4) from (93.2)–(93.3).
2. For the initial model (93.5), prove (93.6) using smoothness at a minimizer.
3. Verify the identity (93.10) from the definition (93.8).
4. Prove \(t_k\ge1+k/2\) by induction and derive a reciprocal-square bound.
5. For \(f(x)=\tfrac L2x^2\), compute the first two accelerated iterates and check the case in which one gradient step reaches the minimizer.
6. Derive the characteristic polynomial (93.15) from (93.14).
7. Formalize IsEstimateModel and prove the model-to-objective-gap lemma independently of any algorithm.
8. Design a structure that packages a finite set of iterates, model functions, weights, and the three estimate-sequence obligations.
9. Give an example showing why a temporary increase in objective value does not contradict the terminal accelerated rate.
10. Compare the potential needed for ordinary gradient descent with the model invariant needed for acceleration.

## 8. Chapter summary

Acceleration changes the proof invariant. The ordinary gradient method uses a squared-distance telescope and obtains an \(O(1/k)\) objective-gap bound. Accelerated methods couple an extrapolated gradient step to an auxiliary model whose weight shrinks like \(1/k^2\). The estimate-sequence inequality converts that shrinking weight directly into an \(O(1/k^2)\) rate.

For Lean, formalize the model bound, the iterate-below-model certificate, and the scalar weight recurrence as separate obligations. Prove the one-step invariant before encoding the whole infinite sequence, and do not assume monotonicity of the objective unless the chosen algorithm actually provides it.

## Further reading

- Nesterov, [“A method of solving a convex programming problem with convergence rate \(O(1/k^2)\)”](https://www.mathnet.ru/eng/dan/v269/i3/p543), the original publication record for accelerated smooth convex optimization.
- Beck and Teboulle, [“A Fast Iterative Shrinkage-Thresholding Algorithm for Linear Inverse Problems”](https://epubs.siam.org/doi/10.1137/080716542), for the proximal accelerated recurrence and its estimate-sequence analysis.
- Mathlib's [gradient interface](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Gradient/Basic.lean) for gradients and their connection to Fréchet derivatives.
