# Chapter 90 — Convexity, Subgradients, and Optimality Certificates

> **Audience.** This chapter assumes comfort with normed spaces, derivatives, and the basic Lean interfaces for linear maps. Its focus is the proof architecture behind convexity and optimization: reducing global claims to line segments, representing nonsmooth first-order information, and separating optimality from existence.

Convex optimization is unusually well suited to formal proof. A local inequality along every segment can certify a global minimum; a short vector inequality can certify the solution of a problem with infinitely many competitors. The formalization challenge is to keep the hypotheses visible. Convexity of the domain, differentiability, membership in the domain, and existence of a minimizer play different roles, even when a paper proof compresses them into one sentence.

This chapter builds a reusable path from convexity to certificates. We first reduce a multivariable statement to a one-dimensional restriction. We then derive the supporting-hyperplane inequality, formulate subgradients for nonsmooth functions, and prove the variational inequality for constrained minima. Finally, we examine strong convexity and a quadratic example, and outline Lean interfaces that let later chapters build algorithms on top of these theorems.

## Learning objectives

After this chapter, you should be able to:

- organize convexity proofs around a segment parameter and its one-dimensional restriction;
- derive a global supporting inequality from differentiable convexity;
- define and use a subgradient predicate that works beyond differentiable functions;
- state constrained first-order optimality with the correct sign;
- distinguish a certificate of optimality from a theorem that a minimizer exists;
- design Lean lemmas that separate geometric, analytic, and optimization hypotheses.

## 1. Convexity is a statement about every chord

Let \(C\) be a subset of a real vector space. It is convex when the segment between any two of its points stays in \(C\):

\[
x,y\in C,\quad t\in[0,1]
\quad\Longrightarrow\quad
(1-t)x+ty\in C.
\tag{90.1}
\]

A real-valued function \(f\) on \(C\) is convex when its value on each chord lies below the corresponding linear interpolation:

\[
f((1-t)x+ty)\le (1-t)f(x)+tf(y).
\tag{90.2}
\]

It helps to draw the proof as a reduction rather than a picture of a curved graph:

~~~text
points x,y in C
      │ choose their segment γ(t) = x + t(y − x)
      ▼
one-variable function φ(t) = f(γ(t)) on [0,1]
      │ prove a scalar chord or derivative inequality
      ▼
substitute t and recover the inequality for f
~~~

In Lean, the set interface is `Convex ℝ C` and the function interface is `ConvexOn ℝ C f`. This distinction matters. Convexity of the set proves that the segment points remain in the domain; convexity of the function supplies the inequality between values. When the domain is the whole vector space, the geometric obligation is trivial, but retaining a domain parameter makes the resulting theorem useful for constraints.

For a proof on a real normed space \(E\), fix \(x,y\in C\) and define

\[
\gamma(t)=x+t(y-x),\qquad \varphi(t)=f(\gamma(t)).
\tag{90.3}
\]

The line restriction φ is convex on the interval whenever \(f\) is convex on \(C\). Conversely, if the chord inequality holds for every pair of endpoints and parameter, it is precisely convexity. This equivalence is the main organizational tool: use the ambient space for geometric membership, but use a scalar parameter for order and differentiation.

### 1.1 Strict convexity and uniqueness

Strict convexity replaces (90.2) by a strict inequality whenever \(x\ne y\) and \(0<t<1\). Suppose \(x_1\) and \(x_2\) are both global minimizers on a convex domain and are distinct. At their midpoint, strict convexity gives

\[
f\left(\frac{x_1+x_2}{2}\right)
<\frac{f(x_1)+f(x_2)}2
=\min_{z\in C}f(z),
\]

which contradicts minimality. Thus strict convexity proves **at most one** minimizer. It does not prove that a minimizer exists. For existence, a separate compactness, coercivity, or completeness argument is needed. Keeping these conclusions separate prevents a common theorem-statement error: uniqueness and existence are different obligations.

## 2. A differentiable convex function lies above its tangent

Suppose \(f\) is convex and differentiable on a convex subset \(C\) of a real inner-product space. At a point \(x\in C\), the derivative determines a linear functional. The inner product represents it by a gradient \(\nabla f(x)\). The key inequality is

\[
f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle
\qquad (y\in C).
\tag{90.4}
\]

The graph of a differentiable convex function therefore lies above each of its tangent hyperplanes. The tangent plane is not merely a local approximation: convexity extends its lower bound to the whole domain.

To prove (90.4), restrict to the chord from \(x\) to \(y\), using φ from (90.3). Convexity yields, for \(0<t\le1\),

\[
\varphi(t)\le (1-t)\varphi(0)+t\varphi(1).
\]

Rearrange and divide by the positive scalar \(t\):

\[
\frac{\varphi(t)-\varphi(0)}t\le \varphi(1)-\varphi(0).
\tag{90.5}
\]

As \(t\) tends to zero from above, the left side tends to the directional derivative at \(x\) in direction \(y-x\), namely \(\langle\nabla f(x),y-x\rangle\). This gives (90.4).

The proof naturally separates into four lemmas: segment membership, convexity of the restricted function, the scalar secant inequality, and identification of the one-sided derivative. The last step is where derivative APIs and scalar inequalities meet. Avoid trying to prove (90.4) by expanding the multivariable definition of differentiability directly; the segment reduction keeps the analytic argument one-dimensional.

Mathlib provides convex-set and convex-function interfaces, along with derivative and gradient interfaces. In a normed space, a Fréchet derivative is a continuous linear map; in a real inner-product space, the Riesz representation identifies this map with a gradient vector. State the general result first for the derivative as a linear functional if possible, and add a gradient corollary when the space supplies the required inner-product structure. This avoids imposing Hilbert-space assumptions on lemmas that only need a continuous linear functional.

### 2.1 A useful certificate shape

Inequality (90.4) can itself be treated as a certificate. If \(g=\nabla f(x)\), then verifying

\[
f(y)-f(x)-\langle g,y-x\rangle\ge0
\]

for every feasible \(y\) proves that \(x\) is globally optimal. An algorithm may find \(x\) approximately; a separate proof can check the hypotheses that make this lower bound valid. This separation between discovery and verification will recur in formalized optimization.

## 3. Subgradients extend the certificate to nonsmooth functions

Differentiability is often too strong. The absolute-value function has a corner at zero, but \(0\) is still its global minimizer. A subgradient describes a supporting linear function without requiring a derivative.

Let \(C\) be a subset of a real inner-product space, \(f:E\to\mathbb R\), and \(x\in C\). A vector \(g\) is a subgradient of \(f\) at \(x\), relative to \(C\), when

\[
f(y)\ge f(x)+\langle g,y-x\rangle
\qquad\text{for every }y\in C.
\tag{90.6}
\]

This is a global inequality, so any such \(g\) certifies that \(x\) is a minimizer if \(g=0\). For the absolute value on ℝ, the subgradients at zero are exactly the scalars \(g\in[-1,1]\): the inequality |y|\ge gy holds for all real \(y\) precisely for those \(g\). The point is that the certificate survives even though the classical derivative does not exist there.

For a custom, domain-relative interface, the predicate can be recorded directly:

~~~lean
def IsSubgradientAt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (f : E → ℝ) (x g : E) : Prop :=
  x ∈ C ∧ ∀ y ∈ C,
    f x + inner ℝ g (y - x) ≤ f y
~~~

This definition deliberately encodes both feasibility and the supporting inequality. Some libraries instead define subdifferentials using extended-real-valued functions or a dual-space functional. Those choices are more general, but they have different API tradeoffs. The custom predicate is enough for finite-dimensional examples and makes the certificate transparent. If the book or a project later adopts a library subdifferential, prove a conversion theorem once rather than changing every downstream result.

### 3.1 Recovering gradients as subgradients

When \(f\) is differentiable and convex, (90.4) says exactly that its gradient is a subgradient. This yields a useful abstraction boundary:

1. use convexity and calculus to prove the gradient is a subgradient;
2. use only the subgradient inequality in optimization theorems;
3. instantiate those theorems for differentiable or nonsmooth models.

The optimization layer no longer needs to know how the vector \(g\) was obtained. It could come from a gradient, a proximal argument, a sum rule, or a manually verified inequality. This is often a better API than proving a separate minimum theorem for every model.

### 3.2 Combining subgradients

For a sum \(f_1+f_2\), if \(g_1\) and \(g_2\) support the respective functions at the same point, adding their inequalities shows that \(g_1+g_2\) supports the sum. The proof is just addition of ordered real inequalities. A rule like this is easy to formalize and composes well.

More delicate rules, such as the exact subdifferential of a sum, may require regularity hypotheses. The direct addition argument proves inclusion of one set of candidate subgradients in another; it does not prove equality. This is a useful example of how formal proof exposes the difference between a safe construction rule and a theorem asserting that all subgradients arise that way.

The following Lean interface makes that one-way rule explicit. The first theorem turns a zero subgradient into a global minimum certificate. The sum theorem assumes certificates for both summands at the same feasible point and constructs one for their sum; it proves the inclusion direction only.

```lean
import Book.Models.FiniteOptimization

open Book.Models.FiniteOptimization

theorem last_is_global_minimum : ∀ x : Candidate, loss last ≤ loss x := by decide

theorem first_optimality_gap_is_four : objectiveGap first = 4 := by decide

def IsSubgradientAt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (f : E → ℝ) (x g : E) : Prop :=
  x ∈ C ∧ ∀ y ∈ C,
    f x + inner ℝ g (y - x) ≤ f y

theorem zero_subgradient_is_minimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {f : E → ℝ} {x : E}
    (h : IsSubgradientAt C f x 0) :
    x ∈ C ∧ ∀ y ∈ C, f x ≤ f y := by
  rcases h with ⟨hx, hs⟩
  refine ⟨hx, fun y hy => ?_⟩
  simpa using hs y hy

theorem subgradient_add
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {f₁ f₂ : E → ℝ} {x g₁ g₂ : E}
    (h₁ : IsSubgradientAt C f₁ x g₁)
    (h₂ : IsSubgradientAt C f₂ x g₂) :
    IsSubgradientAt C (fun z => f₁ z + f₂ z) x (g₁ + g₂) := by
  rcases h₁ with ⟨hx, h₁⟩
  rcases h₂ with ⟨_, h₂⟩
  refine ⟨hx, fun y hy => ?_⟩
  change (f₁ x + f₂ x) + inner ℝ (g₁ + g₂) (y - x) ≤ f₁ y + f₂ y
  rw [inner_add_left]
  have hsum := add_le_add (h₁ y hy) (h₂ y hy)
  linarith
```

## 4. Constrained first-order optimality is a variational inequality

Let \(C\) be convex and \(f\) differentiable. A feasible point \(x_*\in C\) is a global minimizer if

\[
f(y)\ge f(x_*)\qquad\text{for all }y\in C.
\tag{90.7}
\]

By the supporting inequality, a sufficient condition is

\[
\langle\nabla f(x_*),y-x_*\rangle\ge0
\qquad\text{for all }y\in C.
\tag{90.8}
\]

Indeed, (90.4) bounds \(f(y)\) below by \(f(x_*)\) plus the nonnegative term in (90.8). Condition (90.8) is called a variational inequality. It says that the negative gradient cannot point from \(x_*\) toward a feasible first-order descent direction.

For a differentiable convex function, (90.8) is also necessary for a minimizer. Fix any \(y\in C\). By convexity of \(C\), the points \(x_*+t(y-x_*)\) are feasible for \(0\le t\le1\). Minimality implies

\[
f(x_*+t(y-x_*))-f(x_*)\ge0\qquad (0<t\le1).
\]

Divide by \(t>0\) and take the right derivative at zero. The result is (90.8). Thus for differentiable convex optimization over a convex set, (90.8) is equivalent to global optimality.

In the unconstrained case \(C=E\), the condition reduces to \(\nabla f(x_*)=0\). A zero gradient is sufficient by convexity; it is necessary at a differentiable minimum because both positive and negative directions are available. At a boundary point of a constrained domain, only feasible directions are available, so the gradient need not vanish. Using the unconstrained criterion in a constrained theorem is a frequent sign and scope error.

### 4.1 A boundary example

Take \(C=[0,\infty)\) and \(f(x)=(x+1)^2\). The constrained minimizer is \(x_*=0\), but \(f'(0)=2\), so the gradient is not zero. For every feasible \(y\ge0\),

\[
\langle\nabla f(0),y-0\rangle=2y\ge0.
\]

The variational inequality certifies the minimum, and direct expansion makes the same fact visible:

\[
f(y)-f(0)=2y+y^2\ge0.
\]

This is a useful sign check for a formal theorem: at a left endpoint, the positive derivative points toward increasing objective values along every feasible displacement. The negative gradient points outside the feasible half-line.

For a nonsmooth convex function, replace the gradient by a subgradient. The condition \(0\in\partial f(x_*)\), interpreted through (90.6), is again a global minimum certificate. For a constrained problem, one can either use a subgradient inequality stated directly on \(C\), or model the constraint by the indicator function that is zero on \(C\) and \(+\infty\) outside \(C\). The latter approach uses extended-real-valued convex analysis and is more expressive, but it adds a codomain and coercion layer. Start with the relative predicate if that generality is not needed.

### 4.2 Normal-cone interpretation

The feasible directions from \(x_*\) are represented by vectors \(y-x_*\) with \(y\in C\). The normal cone at \(x_*\) consists, under one common sign convention, of vectors \(n\) satisfying

\[
\langle n,y-x_*\rangle\le0\qquad(y\in C).
\]

Then (90.8) says \(-\nabla f(x_*)\) lies in the normal cone. Sign conventions for normal cones differ across texts and libraries, so the theorem should state its inequality explicitly even if it also introduces a bundled normal-cone object. An explicit inequality makes a wrong sign immediately visible.

## 5. Strong convexity gives quantitative conclusions

Suppose \(f\) is μ-strongly convex for some μ>0. In a differentiable inner-product setting, the first-order inequality strengthens to

\[
f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle
 +\frac{\mu}{2}\|y-x\|^2.
\tag{90.9}
\]

At a stationary point \(x_*\), this gives

\[
f(y)-f(x_*)\ge\frac{\mu}{2}\|y-x_*\|^2.
\tag{90.10}
\]

Thus the point is the unique global minimizer, and an objective gap bounds the distance to it:

\[
\|y-x_*\|\le\sqrt{\frac{2(f(y)-f(x_*))}{\mu}}.
\tag{90.11}
\]

The first-order condition gives exact optimality; strong convexity adds stability and an error estimate. In algorithm verification, (90.11) can turn a bound on suboptimality into a bound on solution error.

Strong convexity also illustrates why names alone are not an interface. One definition uses convexity after subtracting the quadratic function \(x\mapsto (\mu/2)\|x\|^2\); another packages the lower bound (90.9). Prove the equivalence needed for the application, then expose the form consumed by the main theorem. Avoid repeatedly expanding a bundled definition through simplification: a named conversion lemma keeps later proofs stable.

## 6. Worked example: quadratic minimization

Let \(E\) be a real inner-product space, \(A:E\to E\) a continuous linear map that is self-adjoint, and \(b\in E\). Consider

\[
f(x)=\frac12\langle Ax,x\rangle-\langle b,x\rangle+c.
\tag{90.12}
\]

Self-adjointness makes the derivative of the quadratic term the map \(h\mapsto\langle Ax,h\rangle\), so

\[
\nabla f(x)=Ax-b.
\tag{90.13}
\]

If \(A\) is positive semidefinite, \(f\) is convex. On the whole space, any solution of the normal equation

\[
Ax=b
\tag{90.14}
\]

is a global minimizer by the zero-gradient criterion. If \(A\) is positive definite with a uniform lower bound \(\langle Av,v\rangle\ge\mu\|v\|^2\) for some μ>0, then \(f\) is strongly convex and the solution, if it exists, is unique.

The finite-dimensional positive-definite case is often solved by linear algebra, but the proof architecture remains valuable. It separates the derivative computation, convexity proof, solution of the linear system, and optimality theorem. If \(A\) is only positive semidefinite, minimizers can fail to be unique; if \(b\) is not in the range of \(A\), a solution to (90.14) need not exist. Convexity alone does not settle either question.

With a convex constraint \(C\), equation (90.14) is no longer generally the right condition. A constrained minimizer \(x_*\) instead satisfies

\[
\langle Ax_*-b,y-x_*\rangle\ge0\qquad(y\in C).
\tag{90.15}
\]

This is an exact certificate. It can prove optimality without explicitly solving for the minimizer, which is useful when \(C\) is given by inequalities and a closed-form solution is unavailable.

## 7. Lean proof architecture

### 7.1 Separate the theorem layers

A maintainable development can expose the following layers:

1. **Geometry:** convexity puts each segment point in \(C\).
2. **Scalar analysis:** convexity on an interval bounds a secant slope by a right derivative.
3. **Differential identification:** the derivative of the restriction is the ambient derivative applied to \(y-x\).
4. **Representation:** in an inner-product space, represent the derivative by the gradient vector.
5. **Optimization:** a supporting inequality or variational inequality proves a global minimum.

The supporting inequality is the bridge between calculus and optimization. Keep it as a separately named lemma with explicit domain membership arguments. Then unconstrained, constrained, and strongly convex results can consume that lemma without repeating the derivative proof.

### 7.2 Choose the right derivative object

Lean's calculus interfaces distinguish derivatives as continuous linear maps from gradients as vectors. A theorem stated for `HasFDerivWithinAt` can apply in a general normed space; a theorem stated using `HasGradientWithinAt` assumes the inner-product representation. Both are useful, but they serve different abstraction levels.

Likewise, derivatives within a set and derivatives on the whole space are not interchangeable without hypotheses. For a constrained point on the boundary, the within-derivative may contain exactly the local information available in feasible directions. A proof that silently uses a full derivative can accidentally assume differentiability beyond the feasible domain. Decide whether the objective is defined and differentiable on an ambient open neighborhood, or whether the theorem only uses within-domain differentiability, and state that choice in the signature.

### 7.3 Keep feasible points explicit

For a domain-relative certificate, a useful invariant is that the supporting point belongs to \(C\), and every comparison point is supplied with membership in \(C\). A theorem should not hide this obligation in a coercion from a subtype unless all callers already use the subtype representation. For a large optimization development, define a feasible-set subtype and package the objective there; for a small theorem library, explicit membership hypotheses may yield simpler statements.

These are two reasonable interface designs:

- use `x : {z // z ∈ C}` and let feasibility be carried by the type;
- use `x : E` and pass `hx : x ∈ C` to each theorem.

The subtype makes invalid candidates unrepresentable but can complicate derivatives and coercions. Explicit hypotheses make ambient calculus easier to state but create more proof obligations. Pick one at the module boundary and avoid switching representations in every lemma.

### 7.4 Package certificates, not solver history

Optimization algorithms often generate iterates, stopping criteria, and approximate gradients. A theorem about global optimality need not trust that history. It can accept a candidate, a feasibility proof, and a supporting inequality as a compact certificate. The computational procedure may be changed independently as long as it still produces data satisfying the certificate interface.

For approximate certificates, expose the error explicitly. If

\[
f(y)\ge f(x)+\langle g,y-x\rangle-\varepsilon
\]

and the linear term has a known lower bound on the feasible set, then \(x\) is ε-optimal up to that bound. Do not call it an exact minimizer. A quantitative theorem should state its norm, objective gap, and feasibility error, since these quantities are not interchangeable.

### 7.5 Avoid overspecifying library names

Mathlib has evolving files and theorem names, while the mathematical interfaces are more stable. Search the current source for `Convex`, `ConvexOn`, `HasFDerivWithinAt`, `HasGradientWithinAt`, and the supporting-hyperplane results before choosing imports. A robust chapter or project note should distinguish the stable concept from the current declaration spelling. Reprove a short bridge lemma only when it improves the local API; do not duplicate a mature general theorem merely to avoid a search.

## 8. Failure modes and repairs

1. **Forgetting convexity of the feasible set.** The segment argument may leave the domain. Add the convex-set hypothesis or restrict to a domain where it is automatic.
2. **Using local minimality as global minimality.** A local minimum need not be global for a nonconvex objective. Use convexity and a supporting inequality.
3. **Using strict convexity to claim existence.** Strict convexity proves at most one minimizer. Add compactness or coercivity for existence.
4. **Setting the gradient to zero at a constrained optimum.** Boundary constraints can block descent. Use (90.8) or a normal-cone condition.
5. **Reversing the variational-inequality sign.** With the convention in (90.8), feasible displacement is \(y-x_*\), so the inner product is nonnegative. Check this against a one-dimensional endpoint example.
6. **Treating a derivative as a gradient without structure.** A derivative is a functional; a gradient vector requires an inner product and a representation theorem.
7. **Assuming differentiability for an absolute-value example.** Use the subgradient inequality directly at the corner.
8. **Proving equality of subdifferentials from one inclusion.** Addition of supporting inequalities proves a candidate rule, not necessarily an exact sum formula.
9. **Hiding feasibility in implicit coercions.** State domain membership or package it consistently in a subtype.
10. **Confusing an approximate certificate with exact optimality.** Keep the error term in the conclusion and quantify what it bounds.

## 9. Exercises

1. Prove that a differentiable convex function on a real vector space has a global minimum at every point where its gradient is zero.
2. Show that for \(f(x)=|x|\) on ℝ, the subgradient set at zero is exactly \([-1,1]\). Identify which \(g\) gives the simplest certificate of the minimum.
3. Let \(C=[0,\infty\)) and \(f(x)=(x+1)^2\). Verify the constrained optimality condition at \(x_*=0\), and explain why the gradient is not zero there.
4. For the quadratic (90.12), derive the derivative formula (90.13) from the difference quotient. Identify where self-adjointness is used.
5. Suppose \(f\) is μ-strongly convex and \(x_*\) is a minimizer. Prove uniqueness directly from the two inequalities obtained by exchanging \(x\) and \(x_*\).
6. Formalize the custom `IsSubgradientAt` predicate. Prove that a zero subgradient certifies minimality, carefully retaining membership in \(C\).
7. Design separate Lean theorem statements for (a) a derivative-valued supporting inequality and (b) its gradient-vector specialization. List the additional assumptions needed for the second theorem.
8. Give a convex function with no minimizer on an open domain. Which hypothesis used by compact-domain existence results fails?
9. Write a one-dimensional test case that detects a reversed sign in the variational inequality for a minimizer at the left endpoint.

## 10. Chapter summary

Convexity is proved one chord at a time. Restricting the objective to the segment between a candidate and a competitor turns the supporting-hyperplane theorem into a scalar secant-slope argument. The resulting inequality says that a gradient is a global lower support, and the same inequality defines subgradients when no derivative exists.

For differentiable convex optimization on a convex set, global optimality is equivalent to the variational inequality that the gradient has nonnegative inner product with every feasible displacement. Unconstrained stationarity is the special case in which all directions are feasible. Strong convexity strengthens the certificate into uniqueness and quantitative error bounds. In Lean, these results become easier to maintain when geometry, scalar calculus, derivative representation, and optimization are separate theorem layers.

## Further reading

- Mathlib's [convex-set interface](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Convex/Basic.lean) for segment-based convexity and convexity lemmas.
- Mathlib's [gradient interface](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Gradient/Basic.lean) for connecting Fréchet derivatives and gradient vectors.
- Boyd and Vandenberghe, *Convex Optimization*, for supporting hyperplanes, subgradients, and optimality conditions.
- Rockafellar, *Convex Analysis*, for a systematic treatment of subdifferentials and normal cones.
