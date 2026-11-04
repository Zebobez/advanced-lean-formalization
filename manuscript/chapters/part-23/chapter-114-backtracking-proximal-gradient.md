# Chapter 114 — Backtracking Proximal Gradient and Local Curvature Certificates

> **Audience.** This chapter follows proximal gradient and forward–backward splitting from Chapters 92 and 113. It removes the need to know a global smoothness constant before choosing a step, using a local quadratic majorization test whose acceptance certificate can be formalized directly.

A fixed proximal-gradient step requires a usable upper bound on the curvature of the smooth loss. In applications the gradient may be inexpensive to evaluate while its best global Lipschitz constant is unknown or very conservative. Backtracking estimates enough curvature for the current move, tests the resulting quadratic model, and increases the estimate only when the test fails.

The line search is part of the proof, not just a numerical convenience. Each accepted estimate certifies that the smooth objective lies below its local quadratic model at the proposed point. That certificate gives monotone objective decrease, a comparator inequality, and—when accepted estimates are bounded above—an \(O(1/N)\) objective-gap guarantee.

## Learning objectives

After this chapter, you should be able to:

- define the proximal quadratic model and its acceptance condition;
- explain why backtracking terminates for a globally smooth convex loss;
- derive descent and comparator inequalities from one accepted step;
- prove an \(O(1/N)\) objective-gap bound under bounded accepted curvature;
- work through line searches with a sparse penalty and a projection constraint;
- represent the search result in Lean as a finite certificate rather than an opaque loop.

## 1. The local quadratic model

### 1.1 Model the smooth term

Consider the composite problem
\[
\min_{x\in H} F(x):=f(x)+g(x),
\tag{114.1}
\]
where \(H\) is a finite-dimensional real inner-product space, \(f:H\to\mathbb R\) is convex and differentiable, and \(g:H\to\mathbb R\cup\{+\infty\}\) is proper, lower-semicontinuous, and convex. Assume its proximal map is computable.

At a point \(x\), replace \(f\) with a first-order model plus a quadratic penalty:
\[
Q_{\ell}(y;x)
=f(x)+\langle\nabla f(x),y-x\rangle
+\frac{\ell}{2}\|y-x\|^2+g(y),
\qquad \ell>0.
\tag{114.2}
\]
The minimizer is a proximal-gradient candidate,
\[
y_{\ell}(x)
=\operatorname{prox}_{g/\ell}\bigl(x-\ell^{-1}\nabla f(x)\bigr).
\tag{114.3}
\]
The coefficient \(\ell\) plays two roles: it controls how far the candidate can move, and it is the curvature certificate required for the quadratic model to dominate \(f\).

The smooth part is majorized at the candidate when
\[
f(y_{\ell}(x))
\le f(x)+\langle\nabla f(x),y_{\ell}(x)-x\rangle
+\frac{\ell}{2}\|y_{\ell}(x)-x\|^2.
\tag{114.4}
\]
This is a local test. A rejected value says only that this trial model was too optimistic for this candidate; a larger value changes the candidate and the test must be repeated.

### 1.2 Why the test eventually passes

If \(\nabla f\) is globally \(L\)-Lipschitz, the descent lemma says that for every \(x,y\),
\[
f(y)\le f(x)+\langle\nabla f(x),y-x\rangle
+\frac L2\|y-x\|^2.
\tag{114.5}
\]
Therefore every trial with \(\ell\ge L\) satisfies (114.4). A geometric search that multiplies \(\ell\) by a fixed factor \(\eta>1\) after each rejection must terminate after finitely many trials.

The algorithm need not be given \(L\); the theorem uses it to prove termination. The search only evaluates the left and right sides of (114.4). For a locally smooth objective, a local Lipschitz bound on the gradient over the relevant segment can serve the same role, but a global convergence theorem then needs to state the corresponding boundedness assumptions.

## 2. A backtracking iteration

### 2.1 Search and update

Fix a growth factor \(\eta>1\), a positive floor \(\ell_{\min}\), and an initial estimate \(\ell_{-1}>0\). At iteration \(k\ge0\), begin with a trial value no larger than the previous accepted value unless the floor applies:
\[
\ell\gets\max\{\ell_{\min},\ell_{k-1}/\eta\}.
\tag{114.6}
\]
For each trial, compute \(y=y_{\ell}(x^k)\). If (114.4) fails, replace \(\ell\) by \(\eta\ell\) and recompute \(y\). Stop at the first accepted value \(\ell_k\), then set \(x^{k+1}=y_{\ell_k}(x^k)\).

The data flow is:

    accepted curvature ℓ(k−1)
              |
              v
    start at max(ℓmin, ℓ(k−1)/η)
              |
              v
    proximal candidate yℓ(xk) ---> test the quadratic majorizer
              |                              |
           reject                          accept
              |                              |
           ℓ ← η ℓ                      x(k+1) ← y
              +---------- repeat             +----> next iteration

Allowing the initial trial to drop by a factor of \(\eta\) avoids carrying a needlessly large estimate forever. The floor prevents the initial trial from approaching zero. The acceptance test, rather than the heuristic initial guess, determines whether a step is valid.

### 2.2 A finite search certificate

The operational algorithm has a loop, but the mathematical transition can be stated without one. A successful step consists of a positive \(\ell_k\), a point \(x^{k+1}\), the proximal optimality condition, and the majorization proof:
\[
\begin{aligned}
&\ell_k>0,\\
&\ell_k(x^k-x^{k+1})-\nabla f(x^k)\in\partial g(x^{k+1}),\\
&f(x^{k+1})\le f(x^k)+\langle\nabla f(x^k),x^{k+1}-x^k\rangle
+\frac{\ell_k}{2}\|x^{k+1}-x^k\|^2.
\end{aligned}
\tag{114.7}
\]
The first two lines identify the proximal candidate; the third is the certificate that the candidate is safe for the true objective. One may additionally retain the number of rejected trials and an equation \(\ell_k=\eta^m\ell_{\mathrm{start}}\). That evidence is useful for proving a bound on \(\ell_k\), but it is not needed to prove descent once (114.7) is available.

This separation is important for formal proof design. Prove existence of a finite accepted trial from smoothness and geometric growth. Prove the algorithmic invariant from the acceptance certificate. The convergence argument can then consume a successful step without unfolding the search loop.

### 2.3 Trial counts and work

For a starting value \(\ell_{\mathrm{start}}>0\), let \(m\) be the least natural number such that \(\eta^m\ell_{\mathrm{start}}\ge L\). Such an \(m\) exists because \(\eta>1\). The descent lemma guarantees acceptance no later than this trial, so the iteration performs at most \(m\) rejections and \(m+1\) proximal candidates. When \(\ell_{\mathrm{start}}<L\), this count is governed by the logarithmic ratio between \(L\) and the trial value; a warm start close to the local curvature can make the extra work small.

This count matters when a proximal map is expensive. Each rejected trial requires a new proximal candidate and an evaluation of the smooth loss at that candidate. A proof of convergence that records only the accepted sequence does not prove an oracle-complexity bound. If the application compares algorithms by gradient or proximal evaluations, retain the rejection counter as part of the state and sum the per-iteration trial counts separately.

An accepted \(\ell_k\) is a local certificate at \(x^k\) and its candidate. It need not be the smallest passing value, and it need not equal a global Lipschitz constant. The rate proof uses a uniform upper bound on accepted values; it does not require the line search to identify exact curvature.

## 3. Descent, comparison, and rates

### 3.1 Objective decrease

Let \(y=x^{k+1}\), \(x=x^k\), and \(\ell=\ell_k\). Since \(y\) minimizes \(Q_\ell(\cdot;x)\), and this model is \(\ell\)-strongly convex,
\[
Q_\ell(y;x)+\frac{\ell}{2}\|y-x\|^2
\le Q_\ell(x;x)=F(x).
\tag{114.8}
\]
The acceptance condition gives \(F(y)\le Q_\ell(y;x)\). Combining the two inequalities yields
\[
F(x^{k+1})\le F(x^k)
-\frac{\ell_k}{2}\|x^{k+1}-x^k\|^2.
\tag{114.9}
\]
Thus every accepted step decreases the objective, and a nonzero step decreases it strictly. This certificate does not require the gradient to be cocoercive with a known modulus. The local test supplies exactly the inequality used by the proof.

### 3.2 A comparator inequality

For any comparison point \(u\) with \(g(u)<+\infty\), proximal optimality implies
\[
g(x^{k+1})-g(u)
\le\left\langle
\ell_k(x^k-x^{k+1})-\nabla f(x^k),
x^{k+1}-u\right\rangle.
\tag{114.10}
\]
Convexity gives \(f(u)\ge f(x^k)+\langle\nabla f(x^k),u-x^k\rangle\), while acceptance bounds \(f(x^{k+1})\) by its quadratic model. Adding these bounds and applying polarization gives
\[
F(x^{k+1})-F(u)
\le\frac{\ell_k}{2}\left(
\|x^k-u\|^2-\|x^{k+1}-u\|^2\right).
\tag{114.11}
\]
The squared step terms cancel because the proximal model and the accepted smoothness model use the same coefficient \(\ell_k\). This is a useful design feature: the line search chooses a model for which the one-step proof closes exactly.

Let \(x^\star\) minimize \(F\), and suppose the accepted curvature values satisfy \(\ell_k\le\bar\ell\). Then (114.11), summed from \(k=0\) to \(N-1\), gives
\[
\sum_{k=0}^{N-1}\bigl(F(x^{k+1})-F(x^\star)\bigr)
\le\frac{\bar\ell}{2}\|x^0-x^\star\|^2.
\tag{114.12}
\]
By monotonicity from (114.9), the last of the \(N\) gaps is no larger than their average:
\[
F(x^N)-F(x^\star)
\le\frac{\bar\ell\|x^0-x^\star\|^2}{2N}.
\tag{114.13}
\]
This is the usual \(O(1/N)\) proximal-gradient objective rate, now expressed using an upper bound on the accepted local curvatures rather than a known sharp global constant.

### 3.3 Bounding the accepted values

Suppose \(\nabla f\) is globally \(L\)-Lipschitz and the line search uses the geometric rule in (114.6). Every trial with \(\ell\ge L\) is accepted by (114.5). If a trial below \(L\) is rejected, its successor is \(\eta\ell\); the first trial at or above \(L\) is therefore less than \(\eta L\). If the initial trial is already accepted, it is bounded by the previous accepted value or the floor.

Consequently, with initial estimate \(\ell_{-1}\), all accepted values admit the uniform bound
\[
\ell_k\le\bar\ell:=\max\{\ell_{-1},\eta\ell_{\min},\eta L\}.
\tag{114.14}
\]
The indexing convention is explicit here: \(\ell_{-1}\) is the estimate supplied before the first iteration. The important ingredients are geometric growth, a positive floor, and a finite upper threshold that guarantees acceptance.

## 4. Worked examples

### 4.1 Sparse regularization with underestimated curvature

Let
\[
f(x)=2x^2,\qquad g(x)=|x|,\qquad x^0=1.
\tag{114.15}
\]
The gradient is \(4x\), so the global Lipschitz constant is \(4\). Start backtracking at \(\ell=1\) and use \(\eta=2\). The candidate is
\[
y_\ell=\operatorname{soft}_{1/\ell}\left(1-\frac4\ell\right).
\tag{114.16}
\]
At \(\ell=1\), this gives \(y=-2\). The smooth model's right side in (114.4) is \(2-12+\tfrac12(9)=-5.5\), while \(f(y)=8\), so the test rejects. At \(\ell=2\), \(y=-\tfrac12\); the model bound is \(2-6+2.25=-1.75\), below \(f(y)=0.5\), so it rejects again. At \(\ell=4\), the candidate is \(0\) and both sides of the majorization test are \(0\). The accepted step reaches the minimizer of \(2x^2+|x|\).

This example shows why the trial must be recomputed after increasing \(\ell\). The acceptance test is not merely a check of a scalar constant for a point held fixed; the point itself depends on the proposed proximal scale.

The following rational Lean block encodes the positive and negative branches of soft thresholding, recomputes the candidate at each curvature, and proves the two rejection inequalities and final acceptance.

```lean
def softThreshold114 (z threshold : ℚ) : ℚ :=
  if z < 0 then -max (-z - threshold) 0 else max (z - threshold) 0

def backtrackingCandidate114 (ell : ℚ) : ℚ :=
  softThreshold114 (1 - 4 / ell) (1 / ell)

def smoothObjective114 (x : ℚ) : ℚ := 2 * x ^ 2

def quadraticModel114 (ell candidate : ℚ) : ℚ :=
  smoothObjective114 1 + 4 * (candidate - 1) +
    ell / 2 * (candidate - 1) ^ 2

def compositeObjective114 (x : ℚ) : ℚ := smoothObjective114 x + |x|

theorem first_trial_candidate_is_negative_two :
    backtrackingCandidate114 1 = -2 := by
  norm_num [backtrackingCandidate114, softThreshold114]

theorem first_trial_fails_majorization :
    quadraticModel114 1 (backtrackingCandidate114 1) <
      smoothObjective114 (backtrackingCandidate114 1) := by
  norm_num [quadraticModel114, smoothObjective114,
    backtrackingCandidate114, softThreshold114]

theorem second_trial_candidate_is_negative_half :
    backtrackingCandidate114 2 = -(1 : ℚ) / 2 := by
  norm_num [backtrackingCandidate114, softThreshold114]

theorem second_trial_fails_majorization :
    quadraticModel114 2 (backtrackingCandidate114 2) <
      smoothObjective114 (backtrackingCandidate114 2) := by
  norm_num [quadraticModel114, smoothObjective114,
    backtrackingCandidate114, softThreshold114]

theorem fourth_trial_candidate_is_zero : backtrackingCandidate114 4 = 0 := by
  norm_num [backtrackingCandidate114, softThreshold114]

theorem fourth_trial_is_accepted :
    smoothObjective114 (backtrackingCandidate114 4) ≤
      quadraticModel114 4 (backtrackingCandidate114 4) := by
  norm_num [quadraticModel114, smoothObjective114,
    backtrackingCandidate114, softThreshold114]

theorem zero_is_global_minimizer_of_composite_example (x : ℚ) :
    compositeObjective114 0 ≤ compositeObjective114 x := by
  unfold compositeObjective114 smoothObjective114
  norm_num
  nlinarith [sq_nonneg x, abs_nonneg x]
```

### 4.2 A nonnegative quadratic with an active constraint

Consider
\[
f(x_1,x_2)=\tfrac12(x_1-2)^2+\tfrac92(x_2+1)^2,
\qquad
g=\iota_{\mathbb R^2_+}.
\tag{114.17}
\]
The gradient Lipschitz constant is \(9\), and the proximal map of \(g\) clips each coordinate below at zero. From \(x^0=(0,1)\), trial \(\ell=3\) gives the projected candidate \(y=(2/3,0)\). The smooth objective is \(f(y)=97/18\), but the majorizer right side is only \(17/6\), so the test fails. Trial \(\ell=6\) gives \(y=(1/3,0)\), with \(f(y)=53/9>14/3\), and also fails. At \(\ell=12\), the candidate is \(y=(1/6,0)\); here \(f(y)=445/72\le47/6\), so the test accepts.

The line search therefore adapts to the curvature in the active coordinate while the proximal operation enforces feasibility. The constrained minimizer is \((2,0)\), found by projecting the unconstrained minimizer \((2,-1)\) onto the nonnegative orthant.

## 5. Lean proof architecture

### 5.1 Make acceptance a proposition

Represent a successful transition with a record containing the new point, the positive curvature parameter, a proximal certificate, and a majorization certificate. For example, at the design level:

    structure BacktrackingStep (H : Type*) [InnerProductSpace ℝ H]
        (f : H → ℝ) (grad : H → H)
        (proxOptimal : ℝ → H → H → Prop) (x y : H) where
      curvature : ℝ
      curvature_pos : 0 < curvature
      prox_optimality : proxOptimal curvature x y
      majorizes :
        f y ≤ f x + inner ℝ (grad x) (y - x)
          + curvature / 2 * ‖y - x‖ ^ 2

This is schematic: in a real development, \(g\) may be extended-valued and the subgradient relation should match the imported convex-analysis API. The record nevertheless illustrates the proof boundary. The descent theorem needs only the accepted majorization and proximal optimality; it does not need to know how many trial values were rejected.

### 5.2 Formalize search termination separately

For termination, prove a lemma that any trial with \(\ell\ge L\) satisfies the majorization predicate. Then prove that geometric multiplication eventually crosses \(L\). A natural implementation certificate records a natural number \(m\) of rejections and the accepted value \(\eta^m\ell_{\mathrm{start}}\). This turns a loop result into finite data plus a proposition that the final candidate passes the test.

Keep the candidate computation inside the predicate for each trial. If \(\ell\) changes, the proximal point changes too. Formalizing a loop that reuses the old candidate would prove a different algorithm.

### 5.3 Prove one step before iterating

First derive (114.9) and (114.11) from a single BacktrackingStep record. Next prove the accepted-curvature bound from the search counter. Finally, apply a finite-sum telescoping lemma and objective monotonicity to obtain (114.13). This layered proof is easier to maintain than a single theorem that unfolds the line-search loop, proximal map, and \(N\)-step recursion at once.

Avoid depending on nonlinear arithmetic automation to prove the Hilbert-space identity. State or rewrite
\[
2\langle x-y,y-u\rangle
=\|x-u\|^2-\|y-u\|^2-\|x-y\|^2,
\tag{114.18}
\]
then close the scalar coefficient comparisons separately. This keeps the geometric argument explicit and the residual algebra small.

## 6. Failure modes and extensions

1. **Testing the wrong point.** The candidate changes with \(\ell\); every rejected trial requires recomputing the proximal point.
2. **Checking only the full objective.** The stated line search certifies a model for \(f\), while \(g\) is handled by the proximal minimization. A different test needs a different proof.
3. **Using an arbitrary descent direction.** The comparator and potential proofs depend on proximal optimality for the same quadratic model.
4. **Assuming a rejected trial proves global nonsmoothness.** Rejection only says this local candidate violates this trial model.
5. **Claiming termination without a smoothness bound.** A global Lipschitz gradient is a simple sufficient hypothesis; local versions need explicit region control.
6. **Claiming the gap rate without bounded accepted curvature.** Each step inequality is weighted by \(\ell_k\). A uniform bound is what permits (114.12).
7. **Confusing the curvature estimate and step size.** The step is \(\gamma_k=1/\ell_k\); a larger estimate means a shorter step.
8. **Adding acceleration without changing the proof.** Accelerated methods require an estimate-sequence or potential invariant adapted to the changing curvature; the basic monotone descent argument is not that proof.
9. **Treating rounded function values as exact evidence.** A floating-point comparison can misclassify a near-equality in (114.4). A verified implementation needs a margin or interval bounds that certify the inequality.

Backtracking can also be combined with inertial extrapolation, nonmonotone tests, or local models beyond a quadratic. Each variation changes either the accepted-step certificate or the potential. Reuse the interface only after proving which invariant remains valid.

## 7. Exercises

1. Prove (114.5) from an \(L\)-Lipschitz gradient using the fundamental theorem of calculus along the segment from \(x\) to \(y\).
2. Show that geometric backtracking terminates in finitely many trials when \(\nabla f\) is globally \(L\)-Lipschitz.
3. Derive (114.9) from strong convexity of \(Q_\ell(\cdot;x)\) and the acceptance condition.
4. Derive the comparator inequality (114.11) by adding proximal optimality and the accepted smoothness bound.
5. Sum (114.11) and explain precisely where monotonicity is needed for the final-iterate estimate.
6. Verify all three line-search trials in the sparse-regularization example.
7. Recompute the projected candidates and majorizer values in the nonnegative quadratic example.
8. Suppose the initial curvature estimate is too large. Explain why the decrease-by-\(\eta\) trial in (114.6) can improve step size without compromising acceptance.
9. Propose a Lean record for a rejected trial and state which fields are needed to prove termination.
10. Describe which invariant would need to replace (114.9) in an accelerated backtracking method.

## 8. Chapter summary

Backtracking proximal gradient chooses a curvature estimate by testing whether the smooth loss lies below a local quadratic model at the proximal candidate. Global Lipschitz continuity guarantees finite termination of geometric search. Every accepted step carries the evidence required for objective descent and a comparator inequality. If the accepted curvature values are uniformly bounded, telescoping yields an \(O(1/N)\) objective-gap guarantee.

In Lean, separate finite-search termination from the accepted-step theorem. Store the proximal condition and majorization proof in a transition certificate, derive descent and comparison once, then use a bound on accepted curvature for the rate. This avoids entangling loop control with convex-analysis arguments.

## Further reading

- Beck and Teboulle, [“A Fast Iterative Shrinkage-Thresholding Algorithm for Linear Inverse Problems”](https://epubs.siam.org/doi/10.1137/080716542), for proximal-gradient models and a backtracking accelerated method.
- Nesterov, [“Gradient Methods for Minimizing Composite Functions”](https://doi.org/10.1007/s10107-012-0629-5), for line-search and accelerated methods for composite objectives.
- Chapters 91–93 and 113, for smooth descent, proximal algorithms, acceleration, and the fixed-step forward–backward method.
