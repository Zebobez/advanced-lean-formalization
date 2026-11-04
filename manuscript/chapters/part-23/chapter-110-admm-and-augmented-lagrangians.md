# Chapter 110 — ADMM, Augmented Lagrangians, and Residual Certificates

> **Audience.** This chapter assumes the proximal and saddle-point tools developed in Chapters 92, 108, and 109. It studies the alternating direction method of multipliers (ADMM) for linearly constrained convex problems, with emphasis on scaled dual variables, primal and dual residuals, and proof interfaces for alternating minimizers.

ADMM is useful when a problem separates into two objective terms but couples their variables through a linear constraint. The algorithm alternates between minimizing in one block and then the other, followed by a dual update. The augmented quadratic penalty stabilizes feasibility while the alternating minimizations preserve the structure of each block.

For formalization, three details deserve special care. The dual update makes one KKT condition hold at every iteration; two residuals track the remaining conditions. Also, an ADMM subproblem may have several minimizers, so an iteration is not always a function until a choice rule is supplied. This chapter makes these facts explicit.

## Learning objectives

After this chapter, you should be able to:

- derive ADMM from the augmented Lagrangian and pass to scaled dual variables;
- state the KKT conditions for a linearly constrained two-block problem;
- derive primal and dual residuals from the two subproblem optimality conditions;
- identify the assumptions behind a standard convex convergence theorem;
- work out ADMM updates for Lasso splitting and consensus averaging;
- design Lean interfaces for possibly nonunique minimizers and finite-horizon certificates.

## 1. The split problem and its optimality conditions

### 1.1 Linear coupling of two objective blocks

Let \(X,Z,W\) be finite-dimensional real inner-product spaces, \(A:X\to W\), \(B:Z\to W\) linear, and \(c\in W\). Let \(f:X\to(-\infty,+\infty]\) and \(g:Z\to(-\infty,+\infty]\) be proper, lower semicontinuous, convex functions. Consider
\[
\begin{aligned}
\min_{x,z}\quad & f(x)+g(z)\\
\text{subject to}\quad & Ax+Bz=c.
\end{aligned}
\tag{110.1}
\]
The variables \(x\) and \(z\) are separate blocks; only the equality constraint couples them. A useful split exposes simple operations in each block. For example, a loss may be evaluated efficiently in \(x\), while a regularizer has a simple proximal map in \(z\).

The unaugmented Lagrangian is
\[
L_0(x,z,y)=f(x)+g(z)+\langle y,Ax+Bz-c\rangle.
\tag{110.2}
\]
A saddle point \((x^\star,z^\star,y^\star)\) satisfies primal feasibility and the two subgradient conditions
\[
\begin{aligned}
Ax^\star+Bz^\star-c&=0,\\
0&\in\partial f(x^\star)+A^*y^\star,\\
0&\in\partial g(z^\star)+B^*y^\star.
\end{aligned}
\tag{110.3}
\]
The adjoints appear by differentiating the linear pairing with respect to each block. If \(f\) and \(g\) are differentiable, replace the subdifferentials by gradients. With indicator functions, (110.3) also includes constrained problems.

### 1.2 Why add a quadratic penalty?

For \(\rho>0\), the augmented Lagrangian is
\[
L_\rho(x,z,y)
=f(x)+g(z)+\langle y,r(x,z)\rangle
+\frac{\rho}{2}\|r(x,z)\|^2,
\qquad
r(x,z)=Ax+Bz-c.
\tag{110.4}
\]
Every feasible point has \(r=0\), so the extra term vanishes on the constraint set. It does not change the constrained primal solutions. Away from feasibility, it changes the geometry of the minimization subproblem and gives the dual iteration information about the residual.

The method of multipliers minimizes \(L_\rho\) jointly over both primal blocks before updating \(y\). ADMM makes one Gauss–Seidel pass instead: minimize first in \(x\), then in \(z\), then update the multiplier. The sequential order is what preserves separability; it is also why the method is not simply “minimize the augmented Lagrangian” in one step.

## 2. The ADMM iteration

### 2.1 Unscaled and scaled forms

Starting from \(z^0,y^0\), define
\[
\begin{aligned}
x^{k+1}&\in\arg\min_x L_\rho(x,z^k,y^k),\\
z^{k+1}&\in\arg\min_z L_\rho(x^{k+1},z,y^k),\\
y^{k+1}&=y^k+\rho(Ax^{k+1}+Bz^{k+1}-c).
\end{aligned}
\tag{110.5}
\]
The last line is dual ascent with step size \(\rho\), applied after both block updates. The symbol \(\in\) emphasizes that a minimizer need not be unique.

Set \(u^k=y^k/\rho\). Completing the square gives
\[
\langle y,r\rangle+\frac{\rho}{2}\|r\|^2
=\frac{\rho}{2}\|r+u\|^2-\frac{\rho}{2}\|u\|^2.
\tag{110.6}
\]
The final term is constant with respect to the primal minimization. The scaled iteration is therefore
\[
\begin{aligned}
x^{k+1}&\in\arg\min_x
\left[f(x)+\frac{\rho}{2}\|Ax+Bz^k-c+u^k\|^2\right],\\
z^{k+1}&\in\arg\min_z
\left[g(z)+\frac{\rho}{2}\|Ax^{k+1}+Bz-c+u^k\|^2\right],\\
u^{k+1}&=u^k+Ax^{k+1}+Bz^{k+1}-c.
\end{aligned}
\tag{110.7}
\]
The scaled state is naturally \((z^k,u^k)\). The \(x\)-update is an intermediate result, computed from the previous state; it is not needed as an independent input to the next iteration.

### 2.2 What the state transition promises

One step has the data flow

~~~text
(zᵏ, uᵏ)
    |
    +-- minimize x-block with zᵏ,uᵏ --> xᵏ⁺¹
    |
    +-- minimize z-block with xᵏ⁺¹,uᵏ --> zᵏ⁺¹
    |
    +-- residual update ----------------> uᵏ⁺¹
    v
(zᵏ⁺¹, uᵏ⁺¹)
~~~

The order is a dependency, not a formatting choice: \(z^{k+1}\) uses the newly computed \(x^{k+1}\), and \(u^{k+1}\) uses both new blocks. Replacing the sequence with simultaneous updates describes a different algorithm.

At the level of convex analysis, standard two-block ADMM is closely connected to Douglas–Rachford splitting applied to an appropriate dual problem. This connection explains why proximal and monotone-operator arguments appear in its convergence theory. For a Lean development focused on a concrete optimization problem, however, it is often clearer to formalize the block minimization certificates and residual identities directly.

## 3. Residuals are approximate KKT certificates

### 3.1 The dual update enforces one condition exactly

Define the primal residual by
\[
r^{k+1}=Ax^{k+1}+Bz^{k+1}-c.
\tag{110.8}
\]
The \(z\)-subproblem optimality condition is
\[
0\in\partial g(z^{k+1})+B^*y^k+\rho B^*r^{k+1}.
\tag{110.9}
\]
Since \(y^{k+1}=y^k+\rho r^{k+1}\), this becomes
\[
0\in\partial g(z^{k+1})+B^*y^{k+1}.
\tag{110.10}
\]
Thus the \(z\)-block stationarity condition is satisfied exactly at every completed iteration. The primal residual measures the remaining failure of feasibility.

The \(x\)-subproblem uses the previous \(z^k\). Its optimality condition can be rewritten as
\[
\rho A^*B(z^{k+1}-z^k)
\in\partial f(x^{k+1})+A^*y^{k+1}.
\tag{110.11}
\]
Define the dual residual
\[
s^{k+1}=\rho A^*B(z^{k+1}-z^k).
\tag{110.12}
\]
When \(s^{k+1}\) is small, the \(x\)-block stationarity condition is nearly satisfied. The pair \((r^{k+1},s^{k+1})\) therefore measures two KKT defects, while (110.10) accounts for the third.

This derivation is valuable in Lean because it explains the sign in the dual residual. One should not memorize (110.12): derive it by replacing \(y^k+\rho r^{k+1}\) with \(y^{k+1}\) in the \(x\)-subproblem certificate. Reversing the subtraction in \(z^{k+1}-z^k\) changes the membership relation's sign.

### 3.2 What the convergence theorem says

A standard finite-dimensional convergence theorem assumes that \(f,g\) are closed, proper, and convex; each subproblem is solved exactly; and the unaugmented Lagrangian has a saddle point. Under these assumptions, the primal residual tends to zero, the objective values approach the optimum, and the multiplier sequence converges to a dual optimum. The primal blocks themselves need not converge without additional assumptions.

This is a convergence statement, not a universal \(O(1/k)\) guarantee for each residual or the last iterate. In particular, ADMM should not be assigned a rate theorem unless the chapter states the extra assumptions and the exact quantity whose rate is proved. The residuals are nevertheless practical stopping quantities because they correspond directly to feasibility and stationarity.

In the scaled form, the multiplier is \(y^k=\rho u^k\). A practical stopping test declares tolerances \(\varepsilon_{\mathrm{pri}},\varepsilon_{\mathrm{dual}}>0\) and checks
\[
\|r^{k+1}\|\le\varepsilon_{\mathrm{pri}},
\qquad
\|s^{k+1}\|\le\varepsilon_{\mathrm{dual}}.
\tag{110.13}
\]
A small primal residual alone does not certify dual stationarity; a small dual residual alone does not certify feasibility. In applications, absolute and relative tolerances can be combined to account for the scale of the constraint data.

## 4. Two worked applications

### 4.1 Lasso by variable splitting

Consider
\[
\min_x \frac12\|Ax-b\|^2+\lambda\|x\|_1.
\tag{110.14}
\]
Introduce \(z\) and impose \(x-z=0\), choosing \(f(x)=\tfrac12\|Ax-b\|^2\), \(g(z)=\lambda\|z\|_1\), \(A_{\mathrm{con}}=I\), and \(B_{\mathrm{con}}=-I\). Here \(A\) is the data matrix, the constraint operators are \(I\) and \(-I\), and \(u\) denotes the scaled dual variable. The scaled ADMM updates become
\[
\begin{aligned}
x^{k+1}
&\in\arg\min_x\left[
\frac12\|Ax-b\|^2+\frac{\rho}{2}\|x-z^k+u^k\|^2
\right],\\
z^{k+1}
&=\operatorname{soft}_{\lambda/\rho}(x^{k+1}+u^k),\\
u^{k+1}
&=u^k+x^{k+1}-z^{k+1}.
\end{aligned}
\tag{110.15}
\]
The first-order condition for the quadratic \(x\)-subproblem is the linear system
\[
(A^*A+\rho I)x^{k+1}=A^*b+\rho(z^k-u^k).
\tag{110.16}
\]
The \(z\)-step is coordinatewise soft thresholding. Thus the nonsmooth penalty never enters the linear solve, and the dense or sparse least-squares structure is isolated in the \(x\)-step. If many iterations use the same \(A\) and \(\rho\), one can factor \(A^*A+\rho I\) once and reuse the factorization.

### 4.2 Two-agent consensus

Suppose two agents hold scalar estimates \(a\) and \(b\) and must agree. They solve
\[
\min_{x_1,x_2,z}\frac12(x_1-a)^2+\frac12(x_2-b)^2
\quad\text{subject to}\quad x_1=z,\;x_2=z.
\tag{110.17}
\]
Take \(x=(x_1,x_2)\), \(f(x)=\tfrac12(x_1-a)^2+\tfrac12(x_2-b)^2\), \(g(z)=0\), \(A_{\mathrm{con}}=I_2\), and \(B_{\mathrm{con}}z=(-z,-z)\). The \(x\)-update separates across agents:
\[
x_i^{k+1}=\frac{a_i+\rho(z^k-u_i^k)}{1+\rho},
\qquad (a_1=a,\;a_2=b).
\tag{110.18}
\]
The consensus update is the average
\[
z^{k+1}=\frac{x_1^{k+1}+u_1^k+x_2^{k+1}+u_2^k}{2},
\qquad
u_i^{k+1}=u_i^k+x_i^{k+1}-z^{k+1}.
\tag{110.19}
\]
At a solution \(x_1=x_2=z\), minimizing the original objective gives \(z=(a+b)/2\). This example shows the decomposition principle: local updates use each agent's own datum, and one small consensus step coordinates them. In higher dimensions, each scalar is replaced by a vector, and the average is taken componentwise.

For a numerical check, set \(a=0\), \(b=2\), \(\rho=1\), and initialize \(z^0=u_1^0=u_2^0=0\). The first local updates are \(x_1^1=0\), \(x_2^1=1\); then \(z^1=\tfrac12\), and the dual variables become \((u_1^1,u_2^1)=(-\tfrac12,\tfrac12)\). On the next step, \(x_1^2=\tfrac12\), \(x_2^2=1\), and \(z^2=\tfrac34\). The primal residual vectors are \((-\tfrac12,\tfrac12)\) and \((-\tfrac14,\tfrac14)\). This finite calculation catches a frequent implementation error: the second local update uses the previous consensus value and dual state, while the consensus update uses the new local values.

The exact rational Lean version names each update in its dependency order. It checks the two local updates, consensus values, scaled dual states, and primal residual vectors.

```lean
def localUpdate110 (datum ρ z u : ℚ) : ℚ :=
  (datum + ρ * (z - u)) / (1 + ρ)

def consensusUpdate110 (xOne uOne xTwo uTwo : ℚ) : ℚ :=
  (xOne + uOne + xTwo + uTwo) / 2

def scaledDualUpdate110 (u x z : ℚ) : ℚ := u + x - z

def xOneFirst110 : ℚ := localUpdate110 0 1 0 0
def xTwoFirst110 : ℚ := localUpdate110 2 1 0 0
def zFirst110 : ℚ := consensusUpdate110 xOneFirst110 0 xTwoFirst110 0
def uOneFirst110 : ℚ := scaledDualUpdate110 0 xOneFirst110 zFirst110
def uTwoFirst110 : ℚ := scaledDualUpdate110 0 xTwoFirst110 zFirst110

def xOneSecond110 : ℚ := localUpdate110 0 1 zFirst110 uOneFirst110
def xTwoSecond110 : ℚ := localUpdate110 2 1 zFirst110 uTwoFirst110
def zSecond110 : ℚ :=
  consensusUpdate110 xOneSecond110 uOneFirst110 xTwoSecond110 uTwoFirst110
def uOneSecond110 : ℚ :=
  scaledDualUpdate110 uOneFirst110 xOneSecond110 zSecond110
def uTwoSecond110 : ℚ :=
  scaledDualUpdate110 uTwoFirst110 xTwoSecond110 zSecond110

theorem first_local_updates :
    xOneFirst110 = 0 ∧ xTwoFirst110 = 1 := by
  norm_num [xOneFirst110, xTwoFirst110, localUpdate110]

theorem first_consensus_and_dual_state :
    zFirst110 = 1 / 2 ∧ uOneFirst110 = -(1 : ℚ) / 2 ∧
      uTwoFirst110 = 1 / 2 := by
  norm_num [zFirst110, uOneFirst110, uTwoFirst110,
    xOneFirst110, xTwoFirst110, localUpdate110,
    consensusUpdate110, scaledDualUpdate110]

theorem second_local_updates :
    xOneSecond110 = 1 / 2 ∧ xTwoSecond110 = 1 := by
  norm_num [xOneSecond110, xTwoSecond110, zFirst110,
    uOneFirst110, uTwoFirst110, xOneFirst110, xTwoFirst110,
    localUpdate110, consensusUpdate110, scaledDualUpdate110]

theorem second_consensus_and_dual_state :
    zSecond110 = 3 / 4 ∧ uOneSecond110 = -(3 : ℚ) / 4 ∧
      uTwoSecond110 = 3 / 4 := by
  norm_num [zSecond110, uOneSecond110, uTwoSecond110,
    xOneSecond110, xTwoSecond110, zFirst110,
    uOneFirst110, uTwoFirst110, xOneFirst110, xTwoFirst110,
    localUpdate110, consensusUpdate110, scaledDualUpdate110]

theorem first_primal_residual :
    (xOneFirst110 - zFirst110, xTwoFirst110 - zFirst110) =
      (-(1 : ℚ) / 2, 1 / 2) := by
  norm_num [zFirst110, xOneFirst110, xTwoFirst110,
    localUpdate110, consensusUpdate110]

theorem second_primal_residual :
    (xOneSecond110 - zSecond110, xTwoSecond110 - zSecond110) =
      (-(1 : ℚ) / 4, 1 / 4) := by
  norm_num [zSecond110, xOneSecond110, xTwoSecond110,
    zFirst110, uOneFirst110, uTwoFirst110, xOneFirst110, xTwoFirst110,
    localUpdate110, consensusUpdate110, scaledDualUpdate110]

theorem consensus_solution_is_the_data_average :
    ((0 : ℚ) + 2) / 2 = 1 := by
  norm_num
```

## 5. Lean proof architecture

### 5.1 Model updates as certificates, not opaque argmin operators

An argmin is mathematical notation for an optimizer, not a computable function. In Lean, a reusable design stores an update together with its optimality certificate. For a convex subproblem, that certificate is typically a subgradient condition; for the Lasso's quadratic block, it may be a linear equation; for soft thresholding, it is a coordinatewise proximal characterization.

Nonuniqueness matters. Proper lower semicontinuous convexity does not by itself guarantee that every arbitrary split subproblem attains its infimum, and it does not make an attained minimizer unique. The theorem's assumptions or the application must establish attainment; then there are two honest interfaces:

1. define a one-step relation saying that the selected \(x^+\) and \(z^+\) satisfy their minimizer specifications and the dual update equation;
2. add hypotheses that ensure unique minimizers, or choose a minimizer noncomputably and expose the choice in the definition.

The relational interface is often better for a theorem about every valid ADMM trajectory. The functional interface is convenient for executable examples but must not hide the choice.

A useful one-step specification takes the old state \((z,u)\) and proposed values \((x^+,z^+,u^+)\). It requires that \(x^+\) minimize the \(x\)-objective with \(z,u\) fixed, that \(z^+\) minimize the \(z\)-objective with \(x^+,u\) fixed, and that \(u^+=u+Ax^++Bz^+-c\). In an order-based formulation, each minimizer field says its objective value is no larger than the value at every competitor. In a subgradient-based formulation, replace those global comparisons by the two convex optimality inclusions. Both interfaces should also record that the selected objective values are finite; otherwise extended-real inequalities can make a purported certificate vacuous.

The direct minimizer specification is mathematically transparent but may be expensive to use repeatedly. The subgradient version is often a better theorem interface once a reusable lemma has shown that, for a convex function, the subgradient condition characterizes a global minimum. This mirrors the book's other optimization chapters: isolate a general optimality certificate, prove the algorithm-specific update satisfies it, and let convergence consume the certificate without unfolding the proximal or linear-solve implementation.

### 5.2 Separate KKT algebra from convergence

Package \(A\) and \(B\) as linear maps with adjoints. State the subproblem certificates abstractly, then prove (110.10) and (110.11) by substituting the multiplier update and rearranging. This is a short algebraic layer that should not depend on any convergence argument.

Next define the residuals as data computed from one transition. Prove a local specification theorem:

~~~text
subproblem optimality + dual update
                 |
                 +--> z-block KKT condition (exact)
                 +--> x-block KKT defect = dual residual
                 +--> feasibility defect = primal residual
~~~

Only then introduce a sequence of transitions. The convergence proof consumes the per-step certificates to establish boundedness or summability facts, depending on the theorem selected. Keep these layers distinct: a theorem that the residuals encode KKT defects is valid for one step, whereas a theorem that the residuals tend to zero needs the full convex convergence assumptions.

### 5.3 Keep objective, feasibility, and stationarity outputs distinct

A useful theorem interface returns a record with named fields for objective convergence, primal residual convergence, and dual variable convergence. Do not replace this with a single vague convergence proposition. Also avoid claiming convergence of \(x^k,z^k\) unless the chosen theorem proves it; the standard result cited here does not require the primal blocks themselves to converge.

For finite horizons, make the index convention explicit. If the state at index \(k\) is \((z^k,u^k)\), one transition produces \(x^{k+1},z^{k+1},u^{k+1}\). Define both residuals from these new values. This convention makes the identity \(u^{k+1}=u^k+r^{k+1}\) immediate and prevents shifting the dual residual by one iteration.

## 6. Common failure modes

1. **Treating ADMM as joint minimization.** It alternates the blocks; joint augmented-Lagrangian minimization is the method of multipliers.
2. **Updating the multiplier too early.** The dual step uses the residual after both new primal blocks are available.
3. **Mixing scaled and unscaled dual variables.** The relation is \(y=\rho u\); their update equations differ by the factor \(\rho\).
4. **Using the primal residual as a full optimality certificate.** It checks feasibility only.
5. **Assigning the wrong sign to the dual residual.** Derive it from the \(x\)-subproblem's optimality condition.
6. **Assuming every subproblem has a unique minimizer.** State uniqueness or retain the minimizer relation.
7. **Claiming convergence of each primal block from the basic theorem.** Objective values and residuals converge under standard assumptions; primal iterates may require stronger hypotheses.
8. **Using a nonconvex objective with a convex convergence theorem.** The convex theorem's assumptions are substantive, not notation.
9. **Reading \(\rho\) as a universal speed control.** It rescales the algorithm and the residuals; a particular choice does not guarantee faster convergence on every problem.

## 7. Exercises

1. Derive the KKT conditions (110.3) from the saddle-point definition of \(L_0\).
2. Complete the square in (110.6), starting from \(y=\rho u\).
3. Derive the scaled update (110.7) from the unscaled iteration.
4. Starting from the \(z\)-subproblem certificate, prove that (110.10) holds exactly.
5. Derive the dual residual relation (110.11) and explain why the sign in (110.12) follows.
6. Derive the normal equations (110.16) for the Lasso split.
7. Verify the consensus update (110.19), then show that the primal optimum is \((a+b)/2\).
8. Give an example where a convex block subproblem has more than one minimizer, and describe how the Lean transition relation represents this.
9. State the three convergence conclusions in the chapter and explain why they do not imply convergence of both primal blocks.
10. Propose a Lean structure for storing a one-step ADMM trajectory and its primal and dual residuals.

## 8. Chapter summary

ADMM addresses a separable objective with a linearly coupled constraint by alternating exact block minimizations and updating a Lagrange multiplier. The scaled form simplifies the update equations, but the equality \(y=\rho u\) must remain explicit when switching conventions.

The dual step enforces the \(z\)-block stationarity condition exactly. The primal residual measures constraint violation, and the dual residual measures the remaining \(x\)-block stationarity defect. Under standard convexity, exact-minimization, and saddle-existence assumptions, these residuals vanish and the objective values converge; the primal blocks need not themselves converge.

In Lean, represent subproblem updates with optimality certificates, acknowledge nonunique minimizers, and prove one-step residual identities before building the convergence theorem. This separation makes the formalization reusable across Lasso, consensus, and other splitting applications.

## Further reading

- Boyd, Parikh, Chu, Peleato, and Eckstein, [“Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers”](https://doi.org/10.1561/2200000016), for the scaled algorithm, residuals, convergence theorem, and applications.
- Eckstein and Bertsekas, [“On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators”](https://doi.org/10.1007/BF01581204), for the operator-splitting connection.
- Chapter 109, for primal–dual hybrid gradient and ergodic gap analysis.
