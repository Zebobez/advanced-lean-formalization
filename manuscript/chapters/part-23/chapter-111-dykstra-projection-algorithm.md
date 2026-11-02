# Chapter 111 — Dykstra’s Algorithm and Projection onto Intersections

> **Audience.** This chapter builds on Hilbert projections from Chapter 92 and proximal splitting from Chapters 109–110. It studies Dykstra’s algorithm as a correction-based method for projecting onto an intersection, and then extends the same structure to the proximal map of a sum.

Alternating projections are a natural way to find a point satisfying several convex constraints: project onto one set, then another, and repeat. But feasibility is not the same as best approximation. If the goal is the point of the intersection nearest to a given input, the algorithm must remember how each projection changed that input. Dykstra’s correction vectors provide this memory.

The corrections also make the method a useful formalization case study. Each update carries a normal-cone or subgradient certificate. A simple invariant relates the original input, the current iterate, and all correction vectors. At a fixed point, this invariant and the local certificates combine into the global projection condition.

## Learning objectives

After this chapter, you should be able to:

- state the best-approximation problem over an intersection of closed convex sets;
- distinguish feasibility by alternating projections from nearest-point projection;
- derive the two-set Dykstra updates and their correction invariant;
- use projection optimality to interpret corrections as normal vectors;
- explain how the method extends from indicator functions to a sum of convex functions;
- design Lean state and transition specifications that expose the invariant.

## 1. Projection onto an intersection

### 1.1 Best approximation is stronger than feasibility

Let \(H\) be a finite-dimensional real inner-product space, and let \(C,D\subseteq H\) be nonempty closed convex sets with \(C\cap D\neq\varnothing\). Given an input \(z\in H\), the best-approximation problem is
\[
\min_{x\in C\cap D}\frac12\|x-z\|^2.
\tag{111.1}
\]
The objective is strongly convex, so its minimizer is unique; it is the projection \(P_{C\cap D}(z)\).

For a closed convex set \(C\), define the normal cone at \(x\in C\) by
\[
N_C(x)=\{v\in H:\ \forall w\in C,\ \langle v,w-x\rangle\le0\}.
\tag{111.2}
\]
The projection characterization says
\[
p=P_C(v)
\quad\Longleftrightarrow\quad
p\in C\ \text{ and }\ v-p\in N_C(p).
\tag{111.3}
\]
This is the projection form of a first-order optimality condition. It is often more useful in a proof than unfolding the minimization of the squared distance.

The characterization follows directly from the geometry of the square. If \(p\in C\) and \(v-p\in N_C(p)\), then for every \(w\in C\),
\[
\|v-w\|^2
=\|v-p\|^2+\|w-p\|^2-2\langle v-p,w-p\rangle
\ge\|v-p\|^2.
\tag{111.4}
\]
Conversely, if \(p=P_C(v)\), compare \(p\) with the segment point \(p+t(w-p)\in C\) for \(0<t\le1\), expand the squared distance, divide by \(t\), and let \(t\) decrease to zero. The resulting inequality is \(\langle v-p,w-p\rangle\le0\). This proof pattern gives a reusable Lean lemma in both directions and avoids relying on a uniqueness theorem whose hypotheses may be hidden.

Ordinary alternating projections repeatedly apply \(P_C\) and \(P_D\). Under standard assumptions they produce a feasible limit, but for general convex sets that limit need not be the best approximation to the original input. The method does not retain the components removed by earlier projections. Dykstra’s method adds correction vectors so those components remain part of the state.

### 1.2 The two-set iteration

Initialize \(x^0=z\) and \(p^0=q^0=0\). For each \(k\ge0\), project first onto \(D\), then onto \(C\):
\[
\begin{aligned}
y^{k+1}&=P_D(x^k+p^k),&
p^{k+1}&=x^k+p^k-y^{k+1},\\
x^{k+1}&=P_C(y^{k+1}+q^k),&
q^{k+1}&=y^{k+1}+q^k-x^{k+1}.
\end{aligned}
\tag{111.5}
\]
The output sequence is \(x^k\); \(y^{k+1}\) is the intermediate projection onto the other set. A standard theorem states that both sequences converge to \(P_{C\cap D}(z)\) in this finite-dimensional setting.

The correction updates immediately give local optimality certificates:
\[
p^{k+1}\in N_D(y^{k+1}),
\qquad
q^{k+1}\in N_C(x^{k+1}).
\tag{111.6}
\]
These are not arbitrary residuals. Each is exactly the displacement from the input of a projection to its projected point.

### 1.3 The correction invariant

For every \(k\), the corrections satisfy
\[
z-x^k=p^k+q^k.
\tag{111.7}
\]
At \(k=0\), both sides are zero. If it holds at \(k\), add the two correction updates:
\[
\begin{aligned}
p^{k+1}+q^{k+1}
&=x^k+p^k-y^{k+1}+y^{k+1}+q^k-x^{k+1}\\
&=p^k+q^k+x^k-x^{k+1}\\
&=z-x^{k+1}.
\end{aligned}
\tag{111.8}
\]
The algorithm therefore has a compact proof-state invariant: the original displacement \(z-x^k\) is decomposed into the two stored corrections.

At a fixed point \(x=y=x^\star\), the projection certificates give \(p\in N_D(x^\star)\) and \(q\in N_C(x^\star)\), while the invariant says \(z-x^\star=p+q\). For any \(w\in C\cap D\),
\[
\langle z-x^\star,w-x^\star\rangle
=\langle p,w-x^\star\rangle+\langle q,w-x^\star\rangle
\le0.
\tag{111.9}
\]
Together with \(x^\star\in C\cap D\), this is exactly the projection characterization for \(P_{C\cap D}(z)\). The global convergence theorem supplies convergence; the invariant and local certificates identify the limit.

The same projection characterization supplies a Pythagorean estimate at each update. If \(a=x^k+p^k\), \(y^{k+1}=P_D(a)\), and \(w\in D\), then
\(\|a-w\|^2\ge\|a-y^{k+1}\|^2+\|y^{k+1}-w\|^2\).
Here \(a-y^{k+1}=p^{k+1}\), so the estimate controls both the correction size and the distance to any feasible comparison point. The \(C\)-projection has an analogous inequality involving \(q^{k+1}\). These are important ingredients in convergence arguments, but neither implies that the uncorrected distance \(\|x^k-z\|\) decreases. A formal proof must retain the correction terms when combining the inequalities.

## 2. Why the corrections matter

### 2.1 A simplex projection by hand

Let \(C=\mathbb R_{\ge0}^3\) and let \(D=\{x\in\mathbb R^3:x_1+x_2+x_3=1\}\). Their intersection is the probability simplex. For \(v=(2,-1,\tfrac12)\), the nearest point in the simplex is \((1,0,0)\). The projection onto \(D\) subtracts the same scalar from each coordinate:
\[
P_D(w)=w-\frac{w_1+w_2+w_3-1}{3}(1,1,1).
\tag{111.10}
\]
The projection onto \(C\) clips negative coordinates to zero.

Run one Dykstra cycle from \(x^0=v\), \(p^0=q^0=0\). The first \(D\)-projection is
\[
y^1=P_D(v)=(\tfrac{11}{6},-\tfrac76,\tfrac13),
\qquad
p^1=v-y^1=(\tfrac16,\tfrac16,\tfrac16).
\tag{111.11}
\]
The subsequent \(C\)-projection and correction are
\[
x^1=P_C(y^1)=(\tfrac{11}{6},0,\tfrac13),
\qquad
q^1=y^1-x^1=(0,-\tfrac76,0).
\tag{111.12}
\]
The intermediate \(x^1\) is nonnegative but does not sum to one. The next \(D\)-step receives \(x^1+p^1=(2,\tfrac16,\tfrac12)\), not \(x^1\); after projection it returns \((\tfrac{13}{9},-\tfrac7{18},-\tfrac1{18})\). The correction prevents the first projection’s discarded information from disappearing. Continuing the cycles yields \((1,0,0)\).

This example is a useful implementation check. A projection onto one constraint set need not satisfy the other constraint, and Dykstra does not require every intermediate point to be feasible. The target is the nearest point in the intersection after the correction state has converged.

### 2.2 More than two sets

For \(m\) nonempty closed convex sets \(C_1,\ldots,C_m\), cycle an active index \(i_n\) and maintain one correction \(q_j\) per set. At each step, project the current point plus the active correction onto \(C_{i_n}\), update that correction by the projection displacement, and leave the other correction entries unchanged. Precisely, define
\[
x^n=P_{C_{i_n}}(x^{n-1}+q_{i_n}^{n-1}),
\qquad
q_{i_n}^{n}=x^{n-1}+q_{i_n}^{n-1}-x^n,
\tag{111.13}
\]
and leave \(q_j^n=q_j^{n-1}\) for \(j\ne i_n\). Starting with all corrections zero, \(z-x^n=\sum_{j=1}^m q_j^n\) follows from the same one-step algebra as (111.8). This formulation suggests a Lean state with a finite index type and a vector of corrections, rather than separate fields for every constraint. Proving a cycle theorem then becomes a matter of showing each single-index update preserves this finite-sum invariant.

## 3. Dykstra’s algorithm for proximal sums

### 3.1 Indicators turn projections into proximal maps

For a closed convex set \(C\), its indicator function is zero on \(C\) and \(+\infty\) outside \(C\). Its proximal map is the projection:
\[
\operatorname{prox}_{\gamma\delta_C}=P_C
\qquad(\gamma>0).
\tag{111.14}
\]
Also, \(\delta_C+\delta_D=\delta_{C\cap D}\). Thus projecting onto \(C\cap D\) is a special case of computing the proximal map of a sum.

Let \(f,g:H\to(-\infty,+\infty]\) be proper lower semicontinuous convex functions with \(\operatorname{dom}f\cap\operatorname{dom}g\neq\varnothing\). For \(\gamma>0\), the proximal version of Dykstra’s algorithm is
\[
\begin{aligned}
y^{k+1}&=\operatorname{prox}_{\gamma g}(x^k+p^k),&
p^{k+1}&=x^k+p^k-y^{k+1},\\
x^{k+1}&=\operatorname{prox}_{\gamma f}(y^{k+1}+q^k),&
q^{k+1}&=y^{k+1}+q^k-x^{k+1},
\end{aligned}
\tag{111.15}
\]
with \(x^0=z\) and \(p^0=q^0=0\). Under these assumptions, the iterates converge to \(\operatorname{prox}_{\gamma(f+g)}(z)\). Taking \(f,g\) to be indicators recovers the projection algorithm.

Proximal optimality interprets the corrections as scaled subgradients:
\[
\frac{p^{k+1}}{\gamma}\in\partial g(y^{k+1}),
\qquad
\frac{q^{k+1}}{\gamma}\in\partial f(x^{k+1}).
\tag{111.16}
\]
Indeed, the first proximal input is \(x^k+p^k\), so the prox optimality formula gives \((x^k+p^k-y^{k+1})/\gamma\in\partial g(y^{k+1})\); the numerator is exactly \(p^{k+1}\). The \(f\)-step gives the second inclusion in the same way. This identity is the main reason to define the corrections as input minus output rather than as output minus input.

At a fixed point, \(z-x=p+q\), so the two inclusions combine into the optimality condition for minimizing
\[
f(x)+g(x)+\frac1{2\gamma}\|x-z\|^2.
\tag{111.17}
\]
The same correction invariant therefore handles both set intersections and sums of nonsmooth convex functions.

The corrections can be read as dual information. In the set case they belong to normal cones; in the function case they belong to scaled subdifferentials. Their sum balances the quadratic pull toward the input \(z\). Each prox step certifies only one component function, and the correction state carries the contribution of the other component between updates. This is why the proximal map of a sum is generally not the composition of the individual proximal maps. The connection to the KKT multipliers in Chapter 110 is structural, not merely a shared use of alternating updates.

### 3.2 A quadratic-plus-sparsity example

Take
\[
f(x)=\frac12\|x-b\|^2,
\qquad
g(x)=\lambda\|x\|_1.
\tag{111.18}
\]
Each component prox is simple:
\[
\operatorname{prox}_{\gamma f}(v)=\frac{v+\gamma b}{1+\gamma},
\qquad
\operatorname{prox}_{\gamma g}(v)=\operatorname{soft}_{\gamma\lambda}(v).
\tag{111.19}
\]
The target proximal map can also be evaluated directly:
\[
\operatorname{prox}_{\gamma(f+g)}(z)
=\operatorname{soft}_{\frac{\gamma\lambda}{1+\gamma}}
\left(\frac{z+\gamma b}{1+\gamma}\right).
\tag{111.20}
\]
In this example the closed form is available, so it acts as a reference value for checking the correction updates. In larger composite models, the individual proximal maps may remain tractable when the proximal map of their sum has no direct formula. Dykstra then supplies an inner algorithm built only from the component prox operators.

For a small check, take \(\gamma=1\), \(b=2\), \(\lambda=\tfrac12\), and input \(z=0\). The target in (111.20) is \(0.75\). Starting from \(x^0=0\), \(p^0=q^0=0\), the first \(g\)-prox gives \(y^1=0\) and \(p^1=0\); the following \(f\)-prox gives \(x^1=1\), \(q^1=-1\). On the next cycle, \(y^2=\operatorname{soft}_{1/2}(1)=1/2\), and the corrected \(f\)-prox uses \(y^2+q^1=-1/2\), giving \(x^2=3/4\). Without the stored \(q^1\), the second step would use \(1/2\) and return \(5/4\). The correction changes the composition into an algorithm for the prox of the sum.

## 4. Lean proof architecture

### 4.1 Specify a projection by its variational certificate

Instead of defining a projection through an opaque minimizer, expose its characterization: the candidate belongs to the set and the projection displacement has nonpositive inner product with every feasible direction. In Lean this separates the set membership proof from the order and inner-product reasoning. Uniqueness follows by applying the characterization to two proposed projections and adding the inequalities.

For a single Dykstra step, package the input, projected point, and correction in one certificate. The projection theorem then yields the normal-cone field in (111.6) without unfolding squared-distance algebra at every iteration.

Prove uniqueness of the projection from the certificate once: if \(p_1,p_2\in C\) both satisfy it for the same input \(v\), test the first certificate at \(p_2\) and the second at \(p_1\), then add. The result is \(\|p_1-p_2\|^2\le0\), hence equality. This lets the algorithm use a genuine projection function in the state transition while keeping existence and uniqueness proof obligations separate from the Dykstra invariant.

When formalizing the set constraints as predicates, make closedness and convexity parameters visible in the projection interface. Then the same transition theorem works for a different family of sets without repeating the correction algebra.

### 4.2 Define the state so the invariant is visible

The two-set state contains \((x,p,q)\); the intermediate point \(y\) may be returned as part of the transition result. Define the transition in the same order as (111.5). Its proof obligations are:

~~~text
projection onto D  --> p⁺ ∈ N_D(y⁺)
projection onto C  --> q⁺ ∈ N_C(x⁺)
two correction updates --> z - x⁺ = p⁺ + q⁺
limit certificate --> x* = P_(C ∩ D)(z)
~~~

The invariant proof is a finite algebraic identity, so it should be independent of convergence. Prove it for one step, then lift it over a sequence by induction. This keeps natural-number indexing and projection optimality in separate lemmas.

### 4.3 Separate local correctness from convergence

There are three distinct theorem layers:

1. **Transition correctness:** each correction is the displacement from a projection input to its output.
2. **Invariant preservation:** the original displacement is the sum of correction vectors.
3. **Convergence and identification:** the algorithm's sequences converge, and a limiting projection certificate identifies the common limit with the nearest point.

The first two are elementary and reusable. The third uses a convergence theorem for Dykstra’s algorithm and the closedness of the sets. A formalization can either prove the convergence result in the book or state a carefully parameterized theorem interface and focus on the invariant and limit identification. Do not silently infer convergence from the fact that every step is a projection.

For the proximal-sum extension, replace normal-cone certificates by subgradient certificates and retain the same state invariant. This is a good example of choosing an abstraction at the right level: projections are one application, while proximal maps are the reusable update interface.

## 5. Common failure modes

1. **Confusing feasibility with nearest-point projection.** Alternating projections target a feasible point; Dykstra’s corrections preserve best-approximation information.
2. **Discarding the correction vectors.** The uncorrected sequence is a different method.
3. **Using the wrong projection input.** Each set receives the current point plus its own correction.
4. **Reversing the correction subtraction.** The correction is projection input minus projected output.
5. **Claiming every intermediate iterate lies in the intersection.** Each projection enforces only one set.
6. **Proving convergence before the invariant.** The correction identity is finite algebra and should be isolated first.
7. **Assuming a prox sum equals the composition of prox maps.** Dykstra uses correction state because prox of a sum is generally not the composition.
8. **Forgetting nonempty intersection or domain assumptions.** State the conditions that make the target projection or proximal minimizer well-defined.
9. **Mixing the output with the intermediate point.** The two sequences have different roles in the recurrence, even though both converge to the target.

## 6. Exercises

1. Prove the projection characterization (111.3) from the variational inequality for squared distance.
2. Verify the two correction normal-cone memberships in (111.6).
3. Prove the invariant (111.7) by induction using the updates (111.5).
4. At a fixed point, derive (111.9) and conclude that the point is \(P_{C\cap D}(z)\).
5. Compute the first Dykstra cycle for the simplex input in Section 2.1.
6. Show that the projection of \((2,-1,\tfrac12)\) onto the probability simplex is \((1,0,0)\).
7. Derive the proximal maps in (111.19) and the direct formula (111.20).
8. Explain why the indicator-function case of (111.15) reduces to (111.5).
9. Generalize the correction invariant to a cyclic algorithm over \(m\) sets.
10. Design a Lean transition structure whose fields encode the two projection certificates and correction updates.
11. State which part of a Dykstra formalization is finite algebra and which part requires a convergence theorem.

## 7. Chapter summary

Dykstra’s algorithm projects onto an intersection by alternating projections with correction vectors. Each correction records the displacement removed by one set, and the sum of the corrections equals the displacement from the original input to the current iterate. At a fixed point, the corrections are normal vectors whose sum certifies projection onto the intersection.

When the sets are replaced by proper lower semicontinuous convex functions, the same method uses proximal maps and computes the proximal map of their sum. In Lean, expose the projection or proximal optimality certificate, prove the correction invariant independently, and connect the limit to the desired best-approximation theorem only after the convergence assumptions are explicit.

## Further reading

- Bauschke and Borwein, [“Dykstra’s Alternating Projection Algorithm for Two Sets”](https://cmps-people.ok.ubc.ca/bauschke/Research/02.pdf), for convergence analysis of the two-set method.
- Bauschke and Combettes, [“A Dykstra-like Algorithm for Two Monotone Operators”](https://cmps-people.ok.ubc.ca/bauschke/Research/51.pdf), for the resolvent and proximal-sum generalizations.
- Chapter 92, for Hilbert projections and proximal maps.
- Chapters 109–110, for primal–dual and augmented-Lagrangian splitting.
