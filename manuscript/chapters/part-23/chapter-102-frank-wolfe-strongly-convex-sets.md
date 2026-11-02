# Chapter 102 — Frank–Wolfe over Strongly Convex Sets

> **Audience.** This chapter assumes the smooth convex optimization and linear-oracle tools from Chapters 90–98. It studies a faster Frank–Wolfe rate that comes from curvature of the feasible set itself, rather than from away steps or active-set correction.

Chapters 99–101 accelerated Frank–Wolfe over polytopes by tracking active atoms and changing their weights. A different route is available when the feasible region is curved. On a strongly convex set, every chord between two feasible points has room to bend inward. The linear minimization oracle can exploit this curvature to produce a stronger descent estimate, even though the algorithm remains the standard toward-step method.

Under strong convexity of both the objective and the feasible set, a standard Frank–Wolfe scheme can achieve an \(O(1/t^2)\) objective-error rate. This lies between the general \(O(1/t)\) guarantee and the linear rate available to some polytope variants. The geometry condition is substantive: a simplex or an \(\ell_1\) ball has flat faces and does not satisfy the same positive-curvature assumption.

## Learning objectives

After this chapter, you should be able to:

- distinguish strong convexity of a function from strong convexity of a set;
- state the norm-based chord-bending condition for a feasible set;
- derive how that condition improves the Frank–Wolfe descent inequality;
- state the \(O(1/t^2)\) rate with its parameters and step rule;
- formalize Euclidean and \(\ell_p\) ball oracles;
- design Lean interfaces for set curvature, dual norms, and scalar rate induction.

## 1. Curvature of the feasible region

### 1.1 Function curvature and set curvature are different assumptions

A function \(f\) is \(\alpha_f\)-strongly convex when its values lie above their tangent models by a quadratic term. For a differentiable function,

\[
f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle
+\frac{\alpha_f}{2}\|y-x\|^2.
\tag{102.1}
\]

A set \(\mathcal K\) is \(\alpha_{\mathcal K}\)-strongly convex when it contains a ball around every proper point on every chord. In a normed vector space, one convenient definition is

\[
\gamma x+(1-\gamma)y
+\gamma(1-\gamma)\frac{\alpha_{\mathcal K}}{2}
\|x-y\|^2 z\in\mathcal K
\tag{102.2}
\]

for all \(x,y\in\mathcal K\), \(\gamma\in[0,1]\), and all \(z\) with \(\|z\|=1\). The term involving \(z\) says that the chord midpoint can be displaced in every unit direction by a radius proportional to \(\gamma(1-\gamma)\|x-y\|^2\).

The parameters \(\alpha_f\) and \(\alpha_{\mathcal K}\) measure different objects. The first controls the objective landscape; the second controls the shape of the feasible region. A smooth strongly convex objective over a polytope satisfies (102.1) but generally fails (102.2). Conversely, a strongly convex ball can be paired with a convex smooth objective that has flat directions.

### 1.2 Why curved chords strengthen a linear oracle

Let \(p_t\) minimize the gradient linearization over \(\mathcal K\), and let \(x_t\) be the current iterate. The standard Frank–Wolfe direction is \(p_t-x_t\). Convexity of \(f\) gives

\[
\langle\nabla f(x_t),p_t-x_t\rangle
\le -h_t,
\qquad h_t=f(x_t)-f(x^\star).
\tag{102.3}
\]

This is the usual descent estimate. It does not account for set curvature.

To use the curvature, take the midpoint \(c_t=(x_t+p_t)/2\) and shift it in a unit direction \(w_t\) that minimizes the gradient pairing. By dual-norm equality, \(w_t\) can be chosen with
\(\langle\nabla f(x_t),w_t\rangle=-\|\nabla f(x_t)\|_*\). The set condition (102.2) with \(\gamma=1/2\) makes

\[
\widetilde p_t
=\frac{x_t+p_t}{2}
+\frac{\alpha_{\mathcal K}}{8}\|p_t-x_t\|^2 w_t
\tag{102.4}
\]

feasible. Since \(p_t\) is the global minimizer of the linearization, its gradient pairing is no larger than that of \(\widetilde p_t\). Combining this comparison with (102.3) gives an additional negative term proportional to
\(\alpha_{\mathcal K}\|p_t-x_t\|^2\|\nabla f(x_t)\|_*\).

That term cancels part of the quadratic remainder in the smoothness bound. The useful consequence is not merely a better estimate in a special direction; it is a recurrence that links objective error to gradient norm and permits a faster step-size choice.

### 1.3 Full-dimensional and affine-hull cases

The norm-dual argument is easiest when \(\mathcal K\) has nonempty interior in the ambient space. A simplex inside a larger Euclidean space is lower-dimensional, so a unit vector chosen in an arbitrary ambient direction may not define a feasible chord displacement.

For a lower-dimensional set, formulate curvature in its affine hull and project the gradient onto the direction subspace parallel to that hull. This avoids asking the geometry condition to move in directions where the set has no room. In Lean, make the ambient space explicit: either work in the affine span as a vector space of differences or carry a subspace and use projected gradients.

## 2. The accelerated Frank–Wolfe estimate

### 2.1 A one-step recurrence

Assume that \(f\) is \(\beta_f\)-smooth and convex, \(\mathcal K\) is \(\alpha_{\mathcal K}\)-strongly convex, and the gradient is measured in the dual norm \(\|\cdot\|_*\). A line-search step minimizes the quadratic smoothness upper model along \(p_t-x_t\):

\[
\eta_t\in\arg\min_{\eta\in[0,1]}
\left\{
\eta\langle\nabla f(x_t),p_t-x_t\rangle
+\frac{\beta_f\eta^2}{2}\|p_t-x_t\|^2
\right\}.
\tag{102.5}
\]

Then \(x_{t+1}=x_t+\eta_t(p_t-x_t)\) stays feasible. The curvature argument above and the descent lemma imply

\[
h_{t+1}
\le h_t\max\left\{
\frac12,\,
1-\frac{\alpha_{\mathcal K}\|\nabla f(x_t)\|_*}{8\beta_f}
\right\}.
\tag{102.6}
\]

The first branch handles a large gradient: the best model step can reach its endpoint and halve the error. The second branch handles a smaller gradient, where the curvature contribution controls the decrease.

Strong convexity of \(f\) gives a lower bound on gradient size in terms of objective error. Strong convexity yields
\(h_t\ge(\alpha_f/2)\|x_t-x^\star\|^2\); convexity and Hölder’s inequality give

\[
\|\nabla f(x_t)\|_*
\ge \sqrt{\frac{\alpha_f}{2}}\sqrt{h_t}.
\tag{102.7}
\]

Set

\[
m=\frac{\sqrt{\alpha_f\alpha_{\mathcal K}}}
{8\sqrt{2}\,\beta_f}.
\tag{102.8}
\]

Substituting (102.7) into (102.6) gives a nonlinear scalar recurrence of the form

\[
h_{t+1}\le h_t\max\left\{\frac12,1-m\sqrt{h_t}\right\}.
\tag{102.9}
\]

This is the key analytical change. The decrease depends on \(\sqrt{h_t}\), not just on a fixed multiple of \(h_t\). A comparison sequence with scale \(1/(t+2)^2\) is stable under this recurrence.

The proof dependencies can be pictured as a chain with one geometric input and one objective-growth input:

~~~text
set chord curvature ───────> stronger linear-oracle comparison
                                      |
smoothness + model line search ──────┴──> one-step error recurrence
                                                  ^
objective strong convexity ──> gradient-error bound
                                                  |
                                                  v
                                    scalar 1/(t+2)^2 induction
~~~

The two branches in (102.9) have different proof roles. If the factor is \(1/2\), then an error bound \(C/(t+2)^2\) immediately contracts enough to fit under \(C/(t+3)^2\). In the other branch, split again according to whether \(h_t\) is below half that comparison bound. If it is, monotonicity suffices. If it is above, then \(\sqrt{h_t}\) has a useful lower bound, so the factor \(1-m\sqrt{h_t}\) is at most \(1-3/(t+2)\) once \(C\ge18m^{-2}\). Multiplying this by the inductive upper bound yields the next denominator. This explains why the proof carries both a smoothness-diameter constant and a curvature constant: one controls the initial scale, the other controls the decrease in the small-gradient branch.

### 2.2 The \(O(1/t^2)\) theorem

Let \(D_{\mathcal K}\) be the diameter of the feasible set in the norm used by the smoothness assumption. With the line-search model (102.5), assume \(f\) is \(\alpha_f\)-strongly convex and \(\beta_f\)-smooth, and \(\mathcal K\) is \(\alpha_{\mathcal K}\)-strongly convex. Then the Frank–Wolfe iterates satisfy

\[
f(x_t)-f(x^\star)
\le
\frac{
\max\left\{\frac92\beta_fD_{\mathcal K}^2,\;18m^{-2}\right\}
}{(t+2)^2},
\qquad t\ge1.
\tag{102.10}
\]

The constants are intentionally displayed because they reveal the dependencies. A large smoothness constant or a large diameter worsens the bound. Weak objective curvature or weak set curvature makes \(m\) small and enlarges the second term. The rate is independent of dimension once these norm-based constants are fixed.

The theorem does not say that Frank–Wolfe on every curved-looking region has a quadratic rate. The set must satisfy a uniform chord-bending inequality such as (102.2) in a specified norm, and the objective must supply a suitable gradient-error relation such as (102.7). A set with a corner, a flat face, or vanishing curvature in relevant directions may have \(\alpha_{\mathcal K}=0\), leaving only the general \(O(1/t)\) guarantee.

The \(O(1/t^2)\) order is also a worst-case boundary for this classical method under uniform assumptions. A 2026 lower-bound result constructs strongly convex quadratic objectives over the Euclidean unit ball for which the number of Frank–Wolfe iterations required to reach error \(\varepsilon\) is at least of order \(1/\sqrt{\varepsilon}\), matching the iteration complexity of (102.10). This does not rule out faster rates for particular problems: extra assumptions on the optimizer’s position can support linear convergence. The distinction is between a rate uniform over all allowed instances and a faster rate for a more restricted class.

### 2.3 A recurrence proof that fits Lean

To prove (102.10), separate the optimization theorem from a sequence lemma. Establish (102.9) for the actual iterate. Then choose a constant \(C\) at least
\(\frac92\beta_fD_{\mathcal K}^2\) and \(18m^{-2}\), and prove by induction that

\[
h_t\le\frac{C}{(t+2)^2}.
\tag{102.11}
\]

At the induction step, split on the maximum in (102.9). If the factor is \(1/2\), the previous bound immediately implies the next one. Otherwise use the threshold between the two branches to bound the product
\(h_t(1-m\sqrt{h_t})\). This produces the factor needed to move from \((t+2)^{-2}\) to \((t+3)^{-2}\).

In Lean, the split is useful rather than incidental. It isolates a manageable scalar inequality from norm geometry, oracle optimality, and smoothness. Put the constants into a structure or hypotheses with positivity fields so that divisions and square roots do not repeatedly generate side goals.

## 3. Worked examples

### 3.1 The Euclidean ball

For a Euclidean ball \(\mathcal K=\{x:\|x\|_2\le R\}\), the set-curvature parameter is \(\alpha_{\mathcal K}=1/R\). Its diameter is \(2R\). Given a nonzero gradient \(g\), the linear oracle is

\[
p=-R\frac{g}{\|g\|_2}.
\tag{102.12}
\]

Indeed, Cauchy–Schwarz gives
\(\langle g,x\rangle\ge-\|g\|_2\|x\|_2\ge-R\|g\|_2\), and the displayed point attains both bounds. If \(g=0\), every point in the ball is a minimizer, so the oracle may return the current point or the origin.

As a concrete objective, take
\(f(x)=\frac12\|x-b\|_2^2\) on the unit ball, with \(b=3e_1\), and initialize at \(x_0=0\). The gradient is \(-3e_1\), so the oracle returns \(p_0=e_1\). The quadratic model has unconstrained step \(3\), which is clipped to \(\eta_0=1\), producing \(x_1=e_1\), the constrained minimizer. This aligned case finishes in one iteration; the theorem is useful for arbitrary starting points and directions, where the chord-curvature argument controls the entire trajectory.

### 3.2 A smooth \(\ell_p\) ball and the limit as \(p\) approaches one

For \(1<p\le2\), the \(\ell_p\) ball of radius \(R\) is strongly convex with parameter \((p-1)/R\) with respect to the \(\ell_p\) norm. Let \(q=p/(p-1)\) be the dual exponent. For a nonzero vector \(g\), a linear minimizer is

\[
p_i=-R\,
\frac{\operatorname{sign}(g_i)|g_i|^{q-1}}
{\|g\|_q^{q-1}}.
\tag{102.13}
\]

Hölder’s inequality proves optimality, and the formula satisfies \(\|p\|_p=R\). For \(p=2\), it reduces to the Euclidean ball formula. At \(p=3/2\), \(q=3\); for \(R=2\) and \(g=(2,-1)\), it gives
\[
p=\left(-\frac{8}{\sqrt[3]{9}^{\,2}},
\frac{2}{\sqrt[3]{9}^{\,2}}\right).
\]
The oracle stays closed form, while the curvature parameter is \(1/(4R)\).

As \(p\) approaches \(1\), the parameter \((p-1)/R\) approaches zero, so the \(O(1/t^2)\) guarantee deteriorates. At \(p=1\), the ball has flat faces and becomes a polytope. Chapter 99’s away-step analysis addresses that geometry through active atoms rather than a positive curvature parameter.

## 4. Lean proof architecture

### 4.1 Package the set-curvature property

Define a proposition or typeclass stating that for every pair \(x,y\in\mathcal K\), mixing coefficient \(\gamma\), and unit direction \(z\), the shifted chord point from (102.2) belongs to \(\mathcal K\). Keep the norm and the curvature constant explicit. Avoid defining “strongly convex set” as a vague geometric predicate with no quantitative parameter; the later rate consumes \(\alpha_{\mathcal K}\).

Prove elementary consequences once:

- the midpoint shift (102.4) is feasible;
- the zero-gradient case can be handled without normalizing a vector;
- diameter bounds control every feasible segment length;
- affine-hull projection preserves the gradient pairing with feasible differences.

These lemmas form the geometry API. The analytic proof should use their conclusions rather than unfold the quantified set definition at every step.

### 4.2 Model dual norms and linear-oracle optimality

The oracle proof needs the relation
\[
\min_{\|z\|\le1}\langle g,z\rangle=-\|g\|_*.
\]
For Euclidean space, Cauchy–Schwarz and a normalized negative gradient prove this when \(g\ne0\); zero gradient is a separate branch. For \(\ell_p\), use Hölder’s inequality and the explicit equality case. A generic oracle certificate can hide this implementation and expose only feasibility and global linear optimality.

The dual-norm API matters because the set-curvature shift is expressed in the primal norm while the gradient decrease is measured in the dual norm. In Lean, make coercions between a continuous linear functional and its dual norm explicit instead of relying on elaboration to infer which norm is intended.

### 4.3 Keep theorem layers separate

A robust development can be divided into four interfaces:

1. **Smoothness:** a segment inequality with constant \(\beta_f\).
2. **Objective growth:** the gradient lower bound (102.7), derived from strong convexity or assumed as an error-bound property.
3. **Set geometry:** the shifted-chord feasibility theorem with \(\alpha_{\mathcal K}\).
4. **Scalar recurrence:** (102.9) implies (102.11).

The oracle and smoothness lemmas establish (102.6); the objective-growth lemma turns it into (102.9); the recurrence proof yields the rate. This separation also supports the weaker objective assumption discussed in the source paper: if one has (102.7) directly, global strong convexity of \(f\) is not needed for the final sequence argument.

## 5. Common failure modes

1. **Confusing set curvature with function curvature.** They are separate hypotheses with separate constants.
2. **Applying the ball formula at zero gradient.** Normalization is undefined; return any feasible minimizer in that case.
3. **Using the primal norm for a gradient estimate.** The gradient magnitude belongs to the dual norm.
4. **Ignoring affine dimension.** A lower-dimensional feasible set needs its affine-hull geometry or a projected gradient.
5. **Assuming curvature from a smooth boundary informally.** The theorem needs a uniform quantitative chord-bending constant.
6. **Claiming a linear rate.** This result gives \(O(1/t^2)\), not geometric convergence.
7. **Forgetting step clipping.** The model minimizer must lie in \([0,1]\); otherwise use the endpoint.
8. **Losing constants during the recurrence proof.** Keep \(m\), \(D_{\mathcal K}\), and \(C\) as named parameters.
9. **Mixing the LMO proof with rate induction.** Prove each norm oracle independently from the scalar recurrence.
10. **Treating \(p=1\) as a limit case with positive curvature.** The parameter vanishes and the geometry changes to a polytope.

## 6. Exercises

1. Show that the Euclidean ball of radius \(R\) satisfies (102.2) with \(\alpha_{\mathcal K}=1/R\).
2. Prove the linear minimizer formula (102.12), including the zero-gradient case.
3. Derive the gradient lower bound (102.7) from strong convexity, convexity, and Hölder’s inequality.
4. Use (102.2) at \(\gamma=1/2\) to derive the shifted point (102.4).
5. Starting from the descent lemma and oracle optimality, prove the one-step estimate (102.6).
6. Verify the dual exponent identity and the \(\ell_p\)-oracle formula (102.13).
7. For \(p=3/2\), \(R=2\), and \(g=(2,-1)\), check that the displayed oracle point has \(\ell_{3/2}\) norm two.
8. Prove by induction that the two-branch recurrence (102.9) implies (102.11) for the stated constant \(C\).
9. Explain why the simplex does not have a positive strong-convexity parameter in its ambient space.
10. Rework the Euclidean example with an initial point not collinear with \(b\), and calculate the model step.
11. State the four Lean interfaces from §4.3 as propositions with explicit norm and positivity assumptions.
12. Replace strong convexity of \(f\) with a direct gradient-error inequality and identify which proof layer changes.

## 7. Chapter summary

Strongly convex feasible sets provide a different route to faster Frank–Wolfe convergence than active-set variants. Their chord geometry permits a feasible inward shift in a direction that reduces the gradient pairing, strengthening the usual descent estimate. With a smooth objective and a suitable gradient-error bound, the resulting scalar recurrence gives an \(O(1/t^2)\) objective rate.

Euclidean balls and \(\ell_p\) balls for \(1<p\le2\) illustrate the combination of set curvature and a simple linear oracle. In Lean, state set curvature quantitatively, keep primal and dual norms distinct, prove oracle formulas as independent certificates, and finish with a scalar recurrence theorem.

## Further reading

- Garber and Hazan, [“Faster Rates for the Frank–Wolfe Method over Strongly-Convex Sets”](https://proceedings.mlr.press/v37/garbera15.html), for the chord-curvature definition, norm-ball examples, and the \(O(1/t^2)\) theorem.
- Halbey et al., [“Lower Bounds for Frank-Wolfe on Strongly Convex Sets”](https://proceedings.mlr.press/v306/halbey26a.html), for a 2026 worst-case lower bound matching the uniform \(O(1/t^2)\) order on the Euclidean ball.
- Chapter 99 — Away-Step Frank–Wolfe and Linear Convergence, for polytopes and active-set removal.
- Chapter 98 — Frank–Wolfe and Projection-Free Optimization, for the general curvature-based \(O(1/t)\) rate.

