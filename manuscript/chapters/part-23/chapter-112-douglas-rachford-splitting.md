# Chapter 112 — Douglas–Rachford Splitting and Monotone Inclusions

> **Audience.** This chapter builds on proximal methods, PDHG, ADMM, and Dykstra’s algorithm from Chapters 92 and 109–111. It introduces resolvents of set-valued monotone operators and the Douglas–Rachford fixed-point method, emphasizing fixed-point certificates, shadow iterates, and formal interfaces for operator graphs.

Many convex problems can be written as finding a zero of a sum of two operators:
\[
0\in A x+B x.
\tag{112.1}
\]
The direct resolvent of \(A+B\) may be expensive, even when the individual resolvents of \(A\) and \(B\) are simple. Douglas–Rachford splitting avoids forming that sum inside a single update. It alternates the two resolvents through a reflected point and a fixed-point iteration.

The algorithm has two kinds of points. The iterated state is a fixed-point variable in the ambient space; a shadow point obtained by applying one resolvent solves the original inclusion. In a formal proof, that distinction is essential. The fixed-point equation is algebraically convenient, while the shadow point carries the optimization meaning.

## Learning objectives

After this chapter, you should be able to:

- define monotone operators, resolvents, and reflected resolvents;
- derive the Douglas–Rachford operator from two resolvents;
- prove that its fixed points correspond to zeros of an operator sum;
- distinguish the fixed-point state from the shadow solution;
- work through scalar and projection examples;
- structure Lean proofs around operator graphs, resolvent specifications, and fixed-point certificates.

## 1. Monotone operators and resolvents

### 1.1 Set-valued operators

Let \(H\) be a finite-dimensional real Hilbert space. A set-valued operator \(A\) assigns a set \(A x\subseteq H\) to each \(x\in H\). It is monotone when
\[
\langle x-y,a-b\rangle\ge0
\quad\text{whenever }a\in A x,\ b\in A y.
\tag{112.2}
\]
It is maximal monotone if its graph cannot be enlarged while preserving monotonicity. Subdifferentials of proper lower semicontinuous convex functions and normal-cone operators of closed convex sets are standard examples.

The graph viewpoint replaces a partially defined choice function by a relation: \((x,a)\) belongs to the graph when \(a\in A x\). This is a natural object for Lean because an operator value may contain multiple vectors. Monotonicity is a proposition over pairs of graph witnesses; maximality is a separate condition.

### 1.2 Resolvents are single-valued regularizations

For \(\gamma>0\), the resolvent \(J_{\gamma A}\) is specified by
\[
x=J_{\gamma A}(v)
\quad\Longleftrightarrow\quad
\frac{v-x}{\gamma}\in A x.
\tag{112.3}
\]
For maximal monotone \(A\), the resolvent is defined for every \(v\) and has a unique value. Uniqueness follows directly from monotonicity. If \(x,y\) both satisfy (112.3), then \((v-x)/\gamma\in A x\) and \((v-y)/\gamma\in A y\); monotonicity yields \(-\|x-y\|^2/\gamma\ge0\), hence \(x=y\).

The resolvent is firmly nonexpansive:
\[
\|J_{\gamma A}(u)-J_{\gamma A}(v)\|^2
\le
\langle J_{\gamma A}(u)-J_{\gamma A}(v),u-v\rangle.
\tag{112.4}
\]
In particular it is nonexpansive. For \(A=\partial f\), the resolvent is the proximal map \(\operatorname{prox}_{\gamma f}\). For \(A=N_C\), it is the metric projection \(P_C\). Thus one operator interface covers the main examples from the previous chapters.

The firm inequality follows from monotonicity without differentiating anything. Put \(x=J_{\gamma A}(u)\), \(y=J_{\gamma A}(v)\), \(a=(u-x)/\gamma\), and \(b=(v-y)/\gamma\). Since \(a\in Ax\) and \(b\in Ay\), monotonicity gives \(\langle x-y,(u-v)-(x-y)\rangle\ge0\). Rearranging yields (112.4). This proof is especially suitable for formalization because its only ingredients are two resolvent certificates and one monotonicity hypothesis.

The reflected resolvent is
\[
R_{\gamma A}=2J_{\gamma A}-I.
\tag{112.5}
\]
Firm nonexpansiveness of \(J_{\gamma A}\) implies that \(R_{\gamma A}\) is nonexpansive. The reflection does not itself solve the inclusion; it supplies the intermediate point used by the splitting map.

## 2. The Douglas–Rachford fixed-point method

### 2.1 Define the splitting operator

Given maximal monotone \(A,B\) and \(\gamma>0\), define
\[
\begin{aligned}
T
&=I-J_{\gamma A}+J_{\gamma B}R_{\gamma A}\\
&=\frac12\left(I+R_{\gamma B}R_{\gamma A}\right).
\end{aligned}
\tag{112.6}
\]
The two formulas are algebraically equal after expanding each reflection. The second expression shows that \(T\) is the average of the identity and a nonexpansive map, so \(T\) is firmly nonexpansive.

To see the last implication explicitly, write \(d=u-v\) and \(e=R_{\gamma B}R_{\gamma A}u-R_{\gamma B}R_{\gamma A}v\). Nonexpansiveness gives \(\|e\|\le\|d\|\), and \(Tu-Tv=(d+e)/2\). Expanding \(\|d+e\|^2\) and using Cauchy–Schwarz proves \(\|Tu-Tv\|^2\le\langle Tu-Tv,d\rangle\). This reusable averaging lemma avoids expanding both reflected resolvents inside the convergence proof.

The Douglas–Rachford iteration is simply
\[
z^{k+1}=Tz^k,
\qquad
x^{k+1}=J_{\gamma A}(z^k).
\tag{112.7}
\]
Here \(z^k\) is the fixed-point state and \(x^{k+1}\) is the shadow sequence. Some references swap \(A\) and \(B\), changing which resolvent defines the shadow; both conventions describe the same splitting idea when written consistently.

### 2.2 Fixed points encode solutions

Suppose \(z^\star\) is a fixed point of \(T\). Let
\[
x^\star=J_{\gamma A}(z^\star).
\tag{112.8}
\]
Since \(Tz^\star=z^\star\), the first expression in (112.6) gives
\[
x^\star=J_{\gamma B}(R_{\gamma A}z^\star).
\tag{112.9}
\]
The first resolvent certificate gives \(a^\star=(z^\star-x^\star)/\gamma\in A x^\star\). Also \(R_{\gamma A}z^\star=2x^\star-z^\star=x^\star-\gamma a^\star\). Applying the second resolvent certificate to (112.9) yields \(-a^\star\in Bx^\star\). Therefore
\[
0\in A x^\star+B x^\star.
\tag{112.10}
\]
The shadow of a fixed point is a zero of the sum.

The converse is constructive. If \(a^\star\in A x^\star\), \(b^\star\in Bx^\star\), and \(a^\star+b^\star=0\), set \(z^\star=x^\star+\gamma a^\star\). Then \(J_{\gamma A}z^\star=x^\star\), \(R_{\gamma A}z^\star=x^\star-\gamma a^\star=x^\star+\gamma b^\star\), and \(J_{\gamma B}R_{\gamma A}z^\star=x^\star\). Thus \(Tz^\star=z^\star\). A solution exists exactly when the splitting map has a fixed point.

The fixed point need not be unique even when the shadow solution is unique. Let \(A=N_{[0,\infty)}\) and \(B=N_{(-\infty,0]}\). Their sum has the unique zero \(x=0\), but \(A(0)=(-\infty,0]\) and \(B(0)=[0,\infty)\), so many opposite graph pairs balance at that same shadow. Each pair can produce a different fixed-point state \(z=\gamma a\). Formal theorem statements should quantify over fixed points and their graph witnesses rather than assume that the state is uniquely determined by the output.

### 2.3 Convergence and the output guarantee

If \(A\) and \(B\) are maximal monotone and \(0\in(A+B)(H)\), then \(T\) has a fixed point. Firm nonexpansiveness makes the state sequence Fejér monotone with respect to the fixed-point set. In finite dimensions, the state converges to a fixed point, and the shadow sequence converges to a zero of \(A+B\). In a general Hilbert space, the corresponding basic conclusion is weak convergence; strong convergence requires additional structure.

For any fixed point \(z^\star\), firm nonexpansiveness gives
\(\|z^{k+1}-z^\star\|^2+\|z^{k+1}-z^k\|^2\le\|z^k-z^\star\|^2\).
Summing over \(k\) shows that the squared state residuals are summable, hence \(z^{k+1}-z^k\to0\). In finite dimensions, boundedness gives cluster points; asymptotic regularity makes each cluster point fixed, and Fejér monotonicity then gives convergence of the full sequence. This short proof outline yields a useful Lean decomposition: first prove the one-step inequality, then its finite telescope, then identify cluster points.

The finite telescope has the explicit form
\(\sum_{k=0}^{N-1}\|z^{k+1}-z^k\|^2\le\|z^0-z^\star\|^2-\|z^N-z^\star\|^2\).
Its proof is independent of the operator graph once firm nonexpansiveness is available. A sequence lemma can then turn summability of nonnegative squared residuals into residual convergence. Keeping this analytic step separate from the inclusion proof prevents the final convergence theorem from becoming one long sequence of rewrites.

This theorem does not provide a uniform \(O(1/k)\) objective rate for the last shadow iterate. It is a convergence result for the fixed-point sequence and its shadow. If an application needs a rate or a finite-iteration certificate, state a separate theorem with its own assumptions.

The decomposition of the state into solution and graph information is

~~~text
fixed-point state zᵏ
        |
        +-- J_(γA) ----------------------> shadow xᵏ⁺¹
        |                                    |
        +-- R_(γA), then J_(γB)             +--> 0 ∈ A x + B x
                 |                          when the state is fixed
                 +--> fixed-point update
~~~

## 3. Two worked examples

### 3.1 A nonnegative scalar quadratic

Minimize \(\tfrac12(x-2)^2\) subject to \(x\ge0\). The optimality condition is
\[
0\in N_{[0,\infty)}(x)+(x-2).
\tag{112.11}
\]
Set \(A=N_{[0,\infty)}\) and \(B(x)=x-2\). Their resolvents are
\[
J_{\gamma A}(v)=\max(v,0),
\qquad
J_{\gamma B}(v)=\frac{v+2\gamma}{1+\gamma}.
\tag{112.12}
\]
Take \(\gamma=1\) and \(z^0=-2\). Then \(J_A(z^0)=0\), \(R_A(z^0)=2\), and \(J_B(R_A(z^0))=2\), so \(z^1=0\). Next \(J_A(0)=0\), \(R_A(0)=0\), \(J_B(0)=1\), hence \(z^2=1\). Thereafter the state follows \(z^{k+1}=(z^k+2)/2\) and tends to \(2\).

The shadow values begin \(0,0,1,\tfrac32,\ldots\) and converge to \(2\). The state is not itself the primal iterate at each step. This distinction is easy to miss when translating a fixed-point theorem into an optimization result.

After the first update, the closed-form recurrence is \(z^{k+1}=(z^k+2)/2\), hence \(z^k=2-2^{2-k}\) for \(k\ge1\). The residual \(z^{k+1}-z^k\) halves on each step. This gives a compact exact example for checking both the resolvent scaling and the reflected input.

### 3.2 Projection onto an interval intersection

Let \(C=[0,\infty)\) and \(D=(-\infty,2]\). The inclusion \(0\in N_C(x)+N_D(x)\) is solved by every \(x\in[0,2]\). Set \(A=N_C\), \(B=N_D\), so the resolvents are projections. With \(\gamma=1\), start from \(z^0=4\):
\[
J_A(4)=4,\qquad R_A(4)=4,\qquad J_B(R_A(4))=2,\qquad T(4)=2.
\tag{112.13}
\]
The next state is fixed: \(J_A(2)=2\), \(R_A(2)=2\), and \(J_B(2)=2\). The shadow at the fixed state is \(2\), a point in the intersection. This example also contrasts two algorithms built from projections: Dykstra’s method in Chapter 111 tracks correction vectors to recover a nearest point, while Douglas–Rachford tracks a reflected fixed-point state and extracts a shadow solution.

## 4. Connections to proximal optimization and ADMM

### 4.1 Convex minimization as a monotone inclusion

For proper lower semicontinuous convex \(f,g\), the inclusion
\[
0\in\partial f(x)+\partial g(x)
\tag{112.14}
\]
encodes minimization of \(f+g\) whenever the subdifferential sum rule applies. Under a standard qualification such as relative-interior overlap of the effective domains, \(\partial(f+g)=\partial f+\partial g\). Douglas–Rachford then computes a minimizer using only \(\operatorname{prox}_{\gamma f}\) and \(\operatorname{prox}_{\gamma g}\).

Without a sum-rule hypothesis, a zero of \(\partial f+\partial g\) is still a meaningful certificate, but it should not be silently identified with every minimizer of \(f+g\). This is the same discipline used in earlier chapters: state the exact inclusion theorem before converting it to an optimization conclusion.

### 4.2 Relation to ADMM

For a linearly constrained two-block problem, ADMM can be represented as Douglas–Rachford splitting on an appropriate dual inclusion. The primal block minimizations correspond to evaluations of dual resolvents, with a change of variables between the ADMM multiplier state and the Douglas–Rachford state. This explains why the methods share proximal certificates and convergence arguments.

The equivalence is at the level of a transformed problem and state. It does not mean the raw ADMM state \((z^k,u^k)\) from Chapter 110 is literally the same variable as \(z^k\) in (112.7). A Lean proof should package the transformation and prove that each algorithm step commutes with it, rather than asserting equality of two differently typed states.

## 5. Lean proof architecture

### 5.1 Start from graph membership

Represent a set-valued operator through a relation \(a\in A(x)\), with monotonicity quantified over two graph witnesses. A resolvent specification can be stated as \(x=J_{\gamma A}(v)\) together with \((v-x)/\gamma\in A(x)\). Prove uniqueness from monotonicity; use maximality for existence and full-domain results.

This separation avoids encoding a multivalued operator as an arbitrary function. It also identifies where classical choice may enter: the resolvent itself is single-valued, but establishing that its defining witness exists uses the maximal-monotone theorem.

A useful interface is a structure containing the state \(z\), its shadow \(x\), and witnesses \(a\in Ax\), \(b\in Bx\) with \(a+b=0\), together with \(z=x+\gamma a\). The fixed-point theorem constructs this certificate from a fixed state; the converse theorem constructs a state from a zero certificate. Keeping these directions separate is valuable when an optimization model supplies a KKT witness but the numerical algorithm evolves fixed-point states.

### 5.2 Prove the fixed-point equivalence before convergence

The fixed-point proof needs only the two resolvent specifications and ring-like vector algebra. Given \(Tz=z\), expose the intermediate values \(x=J_{\gamma A}z\) and \(J_{\gamma B}R_{\gamma A}z\), rewrite the fixed-point equation, and derive the two graph memberships with opposite signs. The converse packages a zero of \(A+B\) into a fixed-point witness \(z=x+\gamma a\).

Prove this equivalence independently from nonexpansiveness and convergence. It becomes the reusable bridge between a fixed-point theorem and the original mathematical problem.

The proof should normalize scalar factors before rewriting. From \(x=J_{\gamma A}z\), retain the witness \(a=(z-x)/\gamma\in Ax\). From \(x=J_{\gamma B}R_{\gamma A}z\), retain \(b=(R_{\gamma A}z-x)/\gamma\in Bx\). The identity \(R_{\gamma A}z=2x-z\) then simplifies \(b=-a\). This witness-oriented proof is robust to later changes in names or to an implementation using graph relations instead of operator functions.

### 5.3 Isolate averagedness and shadow extraction

Prove that each reflected resolvent is nonexpansive, that their composition is nonexpansive, and that averaging it with the identity gives a firmly nonexpansive map. The convergence theorem then consumes this property and the nonempty fixed-point set.

Keep a separate theorem for the shadow \(J_{\gamma A}z^k\). In finite dimensions, continuity of the resolvent transfers strong convergence of the state to convergence of the shadow. In infinite-dimensional Hilbert spaces, use the precise weak-convergence theorem rather than assuming every nonexpansive map preserves weak convergence.

This explicit state-shadow split also improves diagnostics. A small fixed-point residual \(\|Tz^k-z^k\|\) measures progress toward a fixed point, while the shadow graph witnesses measure progress toward the original inclusion. Neither should be renamed as an objective-gap certificate without an additional bound.

## 6. Common failure modes

1. **Treating a set-valued operator as a total function.** Store graph membership and derive resolvent uniqueness separately.
2. **Omitting \(\gamma\) from one resolvent.** The two resolvents in the same DRS operator use the same positive scale.
3. **Reversing the reflected-resolvent order.** \(R_{\gamma B}R_{\gamma A}\) and \(R_{\gamma A}R_{\gamma B}\) define related but differently indexed algorithms.
4. **Calling the state the solution.** The shadow is \(J_{\gamma A}z^k\); the state lives in the fixed-point space.
5. **Proving the wrong fixed-point implication.** A fixed point yields a pair of opposite graph elements at the same shadow point.
6. **Claiming a primal objective rate from convergence alone.** The basic theorem is qualitative unless a rate result is added.
7. **Applying a subgradient sum rule without qualification.** A zero of \(\partial f+\partial g\) and a minimizer of \(f+g\) require a stated link.
8. **Equating ADMM states without a transformation.** The equivalence uses the dual problem and a change of variables.
9. **Claiming strong convergence in an arbitrary Hilbert space.** The basic theorem gives weak convergence there; finite dimensions upgrade weak to strong.

## 7. Exercises

1. Prove uniqueness of the resolvent value from monotonicity.
2. Derive firm nonexpansiveness of \(J_{\gamma A}\) from its graph characterization.
3. Verify the two formulas for \(T\) in (112.6).
4. Prove that a fixed point of \(T\) yields a zero of \(A+B\).
5. Starting with \(x\in A^{-1}(a)\) and \(-a\in Bx\), construct the corresponding fixed point.
6. Compute the first four state and shadow values in the scalar quadratic example.
7. Verify the projection calculation in (112.13).
8. State a qualification under which (112.14) characterizes minimizers of \(f+g\).
9. Explain why the ADMM-to-DRS equivalence requires a state transformation.
10. Propose Lean structures for a maximal monotone graph, a resolvent certificate, and a DRS transition.

## 8. Chapter summary

Douglas–Rachford splitting solves \(0\in A x+B x\) by iterating a firmly nonexpansive fixed-point map built from the resolvents of \(A\) and \(B\). Its fixed points correspond to zeros of the sum, and applying one resolvent to the fixed-point state produces a shadow sequence converging to a solution.

For convex functions, resolvents are proximal maps; for normal cones, they are projections. The method therefore connects proximal minimization, feasibility, and ADMM through monotone-operator structure. In Lean, formalize the operator graph, resolvent certificates, fixed-point equivalence, averagedness, and shadow extraction as separate layers.

## Further reading

- Lions and Mercier, [“Splitting Algorithms for the Sum of Two Nonlinear Operators”](https://doi.org/10.1137/0716071), for the foundational splitting method.
- Eckstein and Bertsekas, [“On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators”](https://doi.org/10.1007/BF01581204), for the resolvent, convergence, and ADMM connections.
- Chapters 109–111, for PDHG, ADMM, Dykstra’s algorithm, and proximal splitting.
