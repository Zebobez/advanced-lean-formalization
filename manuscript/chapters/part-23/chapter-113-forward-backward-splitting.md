# Chapter 113 — Forward–Backward Splitting and Cocoercive Operators

> **Audience.** This chapter assumes familiarity with proximal maps, smooth convex optimization, and the resolvent viewpoint from Chapter 112. It develops the forward–backward method for a sum of a maximal monotone operator and a cocoercive operator, then specializes the result to proximal gradient.

Many models combine a term that is easy to differentiate with a term whose subgradient or proximal map is easy to compute. Trying to differentiate the whole objective can fail because the second term may be nonsmooth. Trying to minimize it directly can be needlessly expensive. Forward–backward splitting uses the two pieces asymmetrically: an explicit forward step evaluates the smooth operator, then an implicit backward step applies a resolvent.

The central question is not merely whether the displayed update looks plausible. We need to know which inclusion its fixed points solve, why the step size makes the update stable, and what kind of convergence theorem applies. These three questions lead to three reusable formal objects: a graph certificate for the inclusion, an averagedness estimate for the iteration, and a potential inequality for a quantitative objective bound.

## Learning objectives

After this chapter, you should be able to:

- state the forward–backward algorithm for \(0\in A x+B x\);
- derive the step-size range from cocoercivity;
- prove that fixed points of the update solve the inclusion;
- specialize the method to proximal gradient and projected gradient;
- distinguish qualitative iterate convergence from an objective-gap rate;
- structure Lean developments around graph witnesses, resolvent certificates, and one-step potentials.

## 1. The operator split

### 1.1 An implicit part and an explicit part

Let \(H\) be a real Hilbert space. We seek \(x^\star\in H\) such that
\[
0\in A x^\star+B x^\star,
\tag{113.1}
\]
where \(A:H\rightrightarrows H\) is maximal monotone and \(B:H\to H\) is single-valued and \(\beta\)-cocoercive for some \(\beta>0\). In graph notation, cocoercivity means
\[
\langle Bx-By,x-y\rangle\ge \beta\|Bx-By\|^2
\quad\text{for all }x,y\in H.
\tag{113.2}
\]

The inclusion is a compact way to write an optimality condition. For proper lower-semicontinuous convex functions \(f\) and \(g\), take \(A=\partial g\) and \(B=\nabla f\). If \(f\) is convex with an \(L\)-Lipschitz gradient, the Baillon–Haddad theorem makes \(\nabla f\) \(1/L\)-cocoercive. Under the appropriate convex subdifferential sum rule, (113.1) is the first-order condition for minimizing \(f+g\).

The split is useful when both component operations are available:

```text
current point x
      |
      +---- evaluate Bx and subtract γ Bx ----> forward point x - γ Bx
                                                   |
                                                   +---- apply J_(γA) ----> next point
```

The forward step needs one evaluation of \(B\). The backward step is the resolvent
\[
J_{\gamma A}=(I+\gamma A)^{-1}.
\tag{113.3}
\]
For a maximal monotone \(A\), this map is everywhere defined and firmly nonexpansive. The combination is called forward–backward because the explicit evaluation precedes the implicit resolvent.

### 1.2 Why the smooth part is cocoercive

Cocoercivity is stronger than Lipschitz continuity for a general operator: it controls the angle between a change in input and its image. By Cauchy–Schwarz, (113.2) implies
\[
\|Bx-By\|\le \frac1\beta\|x-y\|.
\tag{113.4}
\]
The converse is false without additional structure. In particular, an arbitrary Lipschitz map need not be cocoercive.

For a gradient, convexity supplies the missing structure. If \(f\) is convex and differentiable on all of \(H\), and \(\nabla f\) is \(L\)-Lipschitz, then
\[
\langle\nabla f(x)-\nabla f(y),x-y\rangle
\ge \frac1L\|\nabla f(x)-\nabla f(y)\|^2.
\tag{113.5}
\]
This is the Baillon–Haddad inequality. Convexity is essential: smoothness alone gives the descent lemma but not (113.5).

The distinction matters when choosing a formal interface. A structure that records only a Lipschitz bound supports continuity and error estimates. A cocoercivity field supports the nonexpansive forward map and therefore the fixed-point convergence proof. If the map is known to be a convex gradient, one can prove or import the theorem that constructs the latter from the former.

## 2. The forward–backward map

### 2.1 Deriving the update and its step size

The forward–backward operator and iteration are
\[
T_{\mathrm{FB}}=J_{\gamma A}\circ(I-\gamma B),
\qquad
x^{k+1}=T_{\mathrm{FB}}x^k
=J_{\gamma A}(x^k-\gamma Bx^k).
\tag{113.6}
\]
The backward subproblem uses the current forward point as its input. It does not evaluate \(B\) at the unknown next point.

To see why the step size is bounded, put \(d=x-y\) and \(e=Bx-By\). Then
\[
\begin{aligned}
\|(I-\gamma B)x-(I-\gamma B)y\|^2
&=\|d-\gamma e\|^2\\
&=\|d\|^2-2\gamma\langle d,e\rangle+\gamma^2\|e\|^2\\
&\le \|d\|^2-\gamma(2\beta-\gamma)\|e\|^2.
\end{aligned}
\tag{113.7}
\]
Thus \(I-\gamma B\) is nonexpansive when \(0\le\gamma\le2\beta\). If \(0<\gamma<2\beta\), the stronger estimate says it is averaged, with averaging parameter \(\gamma/(2\beta)\). The resolvent \(J_{\gamma A}\) is firmly nonexpansive, hence averaged with parameter \(1/2\). A composition of averaged maps is averaged, so \(T_{\mathrm{FB}}\) is averaged as well.

Strict inequality in the step-size range gives an averaged map, the convenient setting for the basic fixed-point convergence theorem. At the endpoint \(\gamma=2\beta\), the forward map is only guaranteed to be nonexpansive by (113.7); this argument no longer gives averagedness. This is why a theorem should record the strict condition instead of quietly replacing it with a non-strict one.

For a convex \(L\)-smooth gradient, set \(\beta=1/L\). A standard fixed step therefore satisfies
\[
0<\gamma<\frac{2}{L}.
\tag{113.8}
\]
The range \(\gamma\le1/L\) is often selected when proving a simple monotone objective decrease. These are different uses of the step-size assumption: averagedness supports iterate convergence, while the smaller range makes a particular descent estimate nonpositive.

### 2.2 Fixed points are inclusion certificates

The fixed-point equation can be unfolded directly from the resolvent specification:
\[
x=T_{\mathrm{FB}}x
\quad\Longleftrightarrow\quad
x=J_{\gamma A}(x-\gamma Bx)
\quad\Longleftrightarrow\quad
-Bx\in Ax.
\tag{113.9}
\]
The last statement is exactly \(0\in Ax+Bx\). The resolvent characterization is \(u=J_{\gamma A}(v)\) iff \((v-u)/\gamma\in Au\). Substituting \(u=x\) and \(v=x-\gamma Bx\) produces \(-Bx\in Ax\).

This equivalence is useful in both directions. A fixed point yields a mathematical solution; a known solution yields a fixed point of the algorithmic map. It also shows that the iteration variable and solution live in the same space here, unlike the shadow-state distinction in Douglas–Rachford splitting. The certificate is nevertheless operator-valued: the proof should retain the element \(-Bx\) witnessing membership in \(Ax\).

### 2.3 The basic convergence statement

Assume \(\operatorname{zer}(A+B)\ne\varnothing\) and \(0<\gamma<2\beta\). Since the forward–backward map is averaged and its fixed-point set is nonempty, its Picard iterates
\[
x^{k+1}=T_{\mathrm{FB}}x^k
\tag{113.10}
\]
converge weakly in a Hilbert space to a fixed point, hence to a solution of (113.1). In finite-dimensional spaces, weak convergence and strong convergence coincide, so the iterates converge in norm.

The theorem is qualitative. It does not by itself give a rate for the objective values or the norm of the inclusion residual. Adding either conclusion requires extra structure and a corresponding estimate. A small step displacement \(\|x^{k+1}-x^k\|\) is a fixed-point diagnostic; it is not automatically an objective-gap certificate.

## 3. Proximal gradient and constrained minimization

### 3.1 Composite objectives

Consider
\[
\min_{x\in H} F(x):=f(x)+g(x),
\tag{113.11}
\]
where \(f\) is convex and differentiable with \(L\)-Lipschitz gradient, and \(g\) is proper, lower-semicontinuous, and convex. With \(A=\partial g\) and \(B=\nabla f\), (113.6) becomes
\[
x^{k+1}
=\operatorname{prox}_{\gamma g}
\bigl(x^k-\gamma\nabla f(x^k)\bigr).
\tag{113.12}
\]
This is proximal gradient. The forward stage makes a gradient move for the smooth loss. The backward stage applies the proximal map for the nonsmooth penalty.

For \(\gamma\le1/L\), compare the next iterate \(p=x^{k+1}\) with any \(u\). Proximal optimality gives
\[
g(p)-g(u)\le
\left\langle\frac{x^k-p}{\gamma}-\nabla f(x^k),p-u\right\rangle.
\tag{113.13}
\]
Convexity and smoothness give
\[
f(p)-f(u)\le
\langle\nabla f(x^k),p-u\rangle+\frac{L}{2}\|p-x^k\|^2.
\tag{113.14}
\]
Adding (113.13) and (113.14), and using the polarization identity, yields
\[
F(p)-F(u)\le
\frac{\|x^k-u\|^2-\|p-u\|^2}{2\gamma}
-\left(\frac{1}{2\gamma}-\frac L2\right)\|p-x^k\|^2.
\tag{113.15}
\]
Taking \(u=x^k\) first shows \(F(x^{k+1})\le F(x^k)\). Now let \(u=x^\star\) be a minimizer. The left side is the objective gap; for \(\gamma\le1/L\), the last term is nonpositive, so the distance potential telescopes. Monotonicity lets us bound the final gap by the average of the first \(N\) gaps:
\[
F(x^N)-F(x^\star)
\le \frac{\|x^0-x^\star\|^2}{2\gamma N}.
\tag{113.16}
\]
This argument demonstrates a useful formalization pattern: state a one-step inequality for an arbitrary comparator, sum it, and only then specialize to an optimizer. The estimate provides an \(O(1/N)\) objective-gap bound without requiring strong convexity.

### 3.2 Worked example: a scalar sparse penalty

Take
\[
f(x)=\tfrac12(x-3)^2,\qquad g(x)=2|x|.
\tag{113.17}
\]
The gradient \(\nabla f(x)=x-3\) is \(1\)-Lipschitz, and \(\operatorname{prox}_{\gamma g}\) is soft thresholding at \(2\gamma\). With \(\gamma=\tfrac12\), the update is
\[
x^{k+1}
=\operatorname{soft}_{1}\!\left(x^k-\tfrac12(x^k-3)\right)
=\operatorname{soft}_{1}\!\left(\tfrac12x^k+\tfrac32\right).
\tag{113.18}
\]
Starting at \(x^0=0\), all arguments are positive. Therefore \(x^{k+1}=\tfrac12x^k+\tfrac12\), so
\[
x^0=0,\quad x^1=\tfrac12,\quad x^2=\tfrac34,\quad
x^k=1-2^{-k}\longrightarrow1.
\tag{113.19}
\]
The minimizer is \(1\): on the positive half-line the derivative of \(F\) is \(x-1\), while no negative point satisfies the subgradient optimality condition. The example checks the step-size scaling and shows a linear sequence of iterates even though the general theorem only promised qualitative convergence. The stronger behavior comes from this particular one-dimensional quadratic structure.

### 3.3 Worked example: projection onto the simplex

Let \(\Delta=\{x\in\mathbb R^3:x_i\ge0,\ \sum_i x_i=1\}\), and minimize
\[
f(x)=\tfrac12\|x-c\|^2,\qquad c=(1.3,0.8,-0.2),
\tag{113.20}
\]
over \(\Delta\). Encode the constraint by \(g=\iota_\Delta\), whose proximal map is projection onto \(\Delta\). Since \(\nabla f(x)=x-c\) is \(1\)-Lipschitz, choosing \(\gamma=\tfrac12\) gives
\[
x^{k+1}=P_\Delta\!\left(\tfrac12 x^k+\tfrac12c\right).
\tag{113.21}
\]
From \(x^0=(0,1,0)\), the forward point is \((0.65,0.9,-0.1)\). Projection onto the simplex subtracts a common threshold from positive coordinates and clips the rest at zero. Here the threshold is \(0.275\), giving
\[
x^1=(0.375,0.625,0).
\tag{113.22}
\]
The optimizer is \(P_\Delta(c)=(0.75,0.25,0)\). Thus forward–backward splitting combines a gradient evaluation with a constraint projection; it does not require the constrained gradient direction itself to remain feasible.

## 4. Formalizing the proof

### 4.1 Model the graph before the algorithm

For Lean, a set-valued operator can first be represented by a relation \(A(x,a)\), meaning \(a\in Ax\). Monotonicity quantifies over two graph witnesses. Cocoercivity is a property of a total map \(B:H\to H\). This keeps the set-valued and single-valued pieces distinct.

The following is a design sketch, not a claim about exact Mathlib declaration names:

```lean
structure CocoerciveMap (H : Type*) [SeminormedAddCommGroup H] [InnerProductSpace ℝ H] where
  toFun : H → H
  beta : ℝ
  beta_pos : 0 < beta
  cocoercive : ∀ x y,
    beta * ‖toFun x - toFun y‖ ^ 2 ≤
      inner ℝ (toFun x - toFun y) (x - y)

def ResolventSpec {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → H → Prop) (gamma : ℝ)
    (v x : H) : Prop :=
  0 < gamma ∧ A x (gamma⁻¹ • (v - x))
```

Depending on the chosen inner-product API, the order of arguments to inner and coercions should be checked against the project imports. The mathematical interface is the important part: a resolvent value is accompanied by a graph witness. From monotonicity, prove the witness is unique; from maximality, use the theorem that provides existence. Do not hide both steps inside an unexamined choice.

### 4.2 Separate algebra from convergence

Prove the fixed-point equivalence (113.9) using the resolvent specification and linear algebra. It does not need the global convergence theorem. Separately prove the forward map is averaged using (113.7), combine it with firm nonexpansiveness of the resolvent, then apply the fixed-point iteration theorem.

This order keeps automation predictable. In a Lean proof, introduce explicit abbreviations for \(d=x-y\) and \(e=Bx-By\), expand the norm square once, rewrite the inner-product terms, and apply cocoercivity. A tactic such as nlinarith may close the scalar inequality after the Hilbert-space identity is established, but it should not be expected to discover that identity on its own.

For the composite optimization theorem, use a separate proximal certificate containing both the minimization property of the proximal point and its subgradient condition. Then prove the one-step estimate (113.15). A finite-sum lemma telescopes the potential. Keeping this lemma independent from the operator convergence theorem permits either route to be reused: the fixed-point route for inclusions, the potential route for objective rates.

### 4.3 Design around invariants and evidence

A practical development can expose three interfaces:

1. **Problem:** a graph relation \(A\), map \(B\), monotonicity and cocoercivity assumptions, and a nonempty zero set.
2. **Step:** a positive scale, a resolvent certificate, and the update \(J_{\gamma A}(x-\gamma Bx)\).
3. **Guarantee:** fixed-point equivalence, averagedness, and—when minimizing an objective—a one-step comparator inequality.

This design prevents a common proof-state problem: after rewriting the update, Lean sees only nested function applications and the connection to graph membership disappears. Retain the resolvent witness as a named hypothesis, derive the inclusion certificate locally, and use the operator theorem only after the certificate is visible.

## 5. Extensions and failure modes

### 5.1 Backtracking, relaxation, and metric changes

In practice, \(L\) may be unknown. Backtracking chooses a trial step and checks a local descent inequality, reducing the step until the inequality holds. The proof then carries a step-size invariant indexed by the iteration rather than a single constant. Variable-metric methods replace the Euclidean norm with a positive-definite geometry and adjust the cocoercivity condition accordingly. Relaxed iterations add a factor \(\lambda_k\) to the displacement \(T x^k-x^k\); convergence assumptions must constrain those factors.

These extensions reuse the same architecture but change the invariant. A proof for fixed \(\gamma\) should not be presented as proving a backtracking algorithm merely because its update has the same shape.

### 5.2 Common errors

1. **Using Lipschitz continuity in place of cocoercivity.** For a general map, that does not establish the averagedness of \(I-\gamma B\).
2. **Forgetting convexity in Baillon–Haddad.** A smooth nonconvex function may have a Lipschitz gradient without a cocoercive gradient.
3. **Mixing the step-size ranges.** \(0<\gamma<2/L\) supports the averaged-operator convergence argument; \(\gamma\le1/L\) makes the simple objective descent estimate (113.15) nonpositive.
4. **Applying the resolvent at the wrong point.** The update is \(J_{\gamma A}(x-\gamma Bx)\), not \(J_{\gamma A}(x)-\gamma Bx\).
5. **Dropping the factor \(\gamma\) in the graph witness.** From the resolvent, \((v-u)/\gamma\in Au\).
6. **Claiming a rate from averagedness alone.** A quantitative objective rate needs an additional potential inequality and optimizer assumptions.
7. **Treating a small update as a complete certificate.** A residual tolerance only has the interpretation supplied by a theorem relating it to feasibility, stationarity, or objective error.
8. **Proving a subgradient sum identity without qualification.** State conditions under which \(\partial(f+g)=\partial f+\partial g\) is being used.

## 6. Exercises

1. Derive (113.7) from cocoercivity, writing every inner-product and norm expansion.
2. Show that \(I-\gamma B\) is \(\gamma/(2\beta)\)-averaged for \(0<\gamma<2\beta\), using the characterization of averaged maps by a squared-displacement inequality.
3. Prove both directions of (113.9) from the resolvent specification.
4. Explain why the same step-size proof cannot be used for an arbitrary \(L\)-Lipschitz map.
5. Derive (113.15) from (113.13), (113.14), and the polarization identity.
6. Sum the one-step inequality to obtain (113.16), carefully stating where \(\gamma\le1/L\) is used.
7. Recompute the first three iterates in (113.18) from the proximal definition rather than quoting soft thresholding.
8. Verify the simplex projection and optimizer in (113.21)–(113.22) using the threshold formula.
9. Design a Lean proposition for an inclusion certificate \(a\in Ax\) and \(a+Bx=0\). Identify which fields are data and which are proofs.
10. Extend the proximal-gradient example to a nonnegative least-squares problem and identify the forward map and backward map.

## 7. Chapter summary

Forward–backward splitting solves \(0\in Ax+Bx\) by composing the resolvent of a maximal monotone operator with an explicit step for a cocoercive map. Cocoercivity gives the sharp stability calculation behind \(0<\gamma<2\beta\); fixed points of the composition are exactly zeros of the sum. When the operators are a convex subdifferential and a smooth convex gradient, the method is proximal gradient. A separate potential inequality yields the \(O(1/N)\) objective-gap bound for \(\gamma\le1/L\).

For formalization, keep graph membership, resolvent witnesses, averagedness, and objective potentials in distinct lemmas. This lets a qualitative inclusion theorem and a quantitative optimization theorem share the update without conflating their assumptions or conclusions.

## Further reading

- Combettes and Wajs, [“Signal Recovery by Proximal Forward-Backward Splitting”](https://pcombet.math.ncsu.edu/mms1.pdf), for a foundational convergence analysis and signal-recovery applications.
- Bauschke and Combettes, [“The Baillon–Haddad Theorem Revisited”](https://arxiv.org/abs/0906.0807), for cocoercivity of convex gradients and related operator characterizations.
- Chapters 91–92 and 109–112, for gradient descent, proximal maps, PDHG, ADMM, Dykstra, and Douglas–Rachford methods.
