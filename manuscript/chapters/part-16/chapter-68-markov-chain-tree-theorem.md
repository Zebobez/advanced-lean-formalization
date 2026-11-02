# Chapter 68 — The Markov Chain Tree Theorem

> **Audience.** This chapter assumes finite-state generators, irreducibility, matrix determinants, and the graph language from Chapters 65–67. It presents a combinatorial formula for stationary weights of a finite irreducible continuous-time chain.

Solving the stationary equations πQ=0 is a linear-algebra problem, but it does not always reveal why the answer has its particular form. The Markov chain tree theorem expresses each stationary weight as a sum over directed spanning trees. Every tree points toward the state it supports, and its weight is the product of its edge rates. The theorem applies without reversibility and can expose structure hidden by a direct matrix solve.

The proof connects three interfaces: directed combinatorics, Laplacian cofactors, and the left nullspace of a generator. Mathlib provides the determinant, adjugate, and finite simple-graph ingredients, but the weighted directed tree expansion must be developed for the chosen rate convention. Keeping that boundary explicit makes the formalization manageable.

## Learning objectives

By the end of the chapter, you should be able to:

- define a directed spanning tree rooted at a state and its rate weight;
- state the cofactor form of the Markov chain tree theorem;
- derive stationary weights from the adjugate of the generator Laplacian;
- compute a stationary law for a directed cycle using trees;
- explain why reversibility is not required;
- plan a Lean proof around finite tree sums, cofactors, and nullspaces.

## 1. Generator conventions and directed trees

Let S be a finite state type and let \(q(i,j)\geq0\) be the jump rate from i to j for \(i\ne j\). Put \(q(i,i)=0\), and define the generator by
\[
  Q(i,j)=q(i,j)\quad(i\ne j),\qquad
  Q(i,i)=-\sum_{j\ne i}q(i,j).
\]
Rows sum to zero, and observables are columns, so \((Qf)(i)=\sum_jQ(i,j)f(j)\). Define the row Laplacian \(L=-Q\). Its off-diagonal entries are \(-q(i,j)\), its diagonal is the total exit rate, and its row sums vanish.

A directed spanning tree rooted at r is a choice of one outgoing parent edge from every vertex except r, with no outgoing edge from r, such that repeatedly following parent edges reaches r. All edges point toward the root. The tree weight is
\[
  w(T)=\prod_{u\ne r}q(u,p_T(u)).
\]
Define τ_r as the sum of these weights over all trees rooted at r. If no such tree exists, the empty sum is zero. In a strongly connected directed rate graph, every root has at least one positive-weight tree, so τ_r>0.

The orientation convention is essential. A tree rooted at r carries flow inward along its directed edges; choosing edges pointing away from r would produce a different cofactor convention. Fix the orientation in the definition and verify it on a two-state chain before applying a library determinant theorem.

## 2. Cofactors of the generator Laplacian

For each r, delete row r and column r from L and call the resulting principal minor \(L^{(r)}\). The directed matrix-tree theorem states
\[
  \det L^{(r)}=\tau_r.
\]
This equality turns a combinatorial sum into a determinant. One proof expands the determinant as a sum over permutations and expands every diagonal entry as a sum of outgoing rates. Terms corresponding to directed cycles away from the root cancel in sign-reversing pairs; the surviving terms select exactly one parent edge per nonroot vertex and form a tree toward r.

For formalization, this cancellation proof is finite but combinatorially dense. A more modular route proves a weighted directed matrix-tree theorem for an arbitrary rate matrix, then instantiates it with the chain generator. The proof can be organized by induction on the number of states, separating trees that use a selected edge from those that do not. Either route should state the principal-minor indexing carefully: the root row and root column are both removed.

The row/column convention can be diagnosed from the directed graph before any determinant expansion. For the row Laplacian, row i records rates leaving i, so the parent map assigns each nonroot vertex an outgoing edge on its route to the root. If instead one defines a column Laplacian whose columns sum to zero, the same cofactor statement is transposed: the interpretation of an arborescence must be changed or the matrix must be transposed. In Lean, encode the matrix convention in a named definition and prove its row-sum or column-sum identity immediately. This prevents later cofactor lemmas from carrying an ambiguous “Laplacian” hypothesis.

The theorem is also called the Markov chain tree formula. It is important to distinguish the formula from a mere statement that cofactors lie in the kernel: the latter is linear algebra, while identifying each cofactor with a positive tree sum is the combinatorial content. If the downstream goal only needs a stationary vector, the determinant cofactor formula may suffice; if positivity, asymptotics, or parameter dependence matters, retain the tree-sum representation.

The cofactor theorem also proves positivity without solving the stationary equations. Under strong connectivity, choose directed paths from each vertex to r and prune cycles to obtain a rooted arborescence. Its rate product is positive; hence the sum τ_r is positive. In Lean, keep the combinatorial existence of a tree separate from nonnegativity of all tree weights.

## 3. From cofactors to stationary weights

The row sums of L vanish, so the constant vector 1 lies in the right kernel. If the chain is irreducible, the kernel is one-dimensional and rank L is |S|−1. The adjugate identity
\[
  L\,\operatorname{adj}(L)=\det(L)I=0
\]
shows every column of adj(L) lies in the right kernel, hence is constant. The diagonal entry at r is the principal cofactor τ_r. It follows that
\[
  \operatorname{adj}(L)_{i,r}=\tau_r
\]
for all i. Since adj(L)L=0, its row \((\tau_r)_r\) is a left null vector of L, equivalently a left stationary vector of Q:
\[
  \sum_i\tau_iQ(i,j)=0\quad\text{for each }j.
\]
Normalize to obtain
\[
  \pi(r)=\frac{\tau_r}{\sum_s\tau_s}.
\]
The denominator is positive because each τ_r is positive.

The argument uses the adjugate rather than explicitly solving a linear system. Mathlib’s matrix adjugate API provides the two multiplication identities and expresses diagonal adjugate entries through row-replacement determinants; determinant development supplies the cofactor manipulations. The tree expansion remains a separate theorem. If the installed API uses a different row/column convention than the mathematical statement, verify the final left-kernel equation by expanding one coordinate.

## 4. Worked example: an oriented three-cycle

Take states 0, 1, and 2 with rates \(0\to1\) equal to a, \(1\to2\) equal to b, and \(2\to0\) equal to c, all positive. The only incoming tree to root 0 uses \(1\to2\) and \(2\to0\), so τ_0=bc. Similarly, τ_1=ca and τ_2=ab. The stationary distribution is
\[
  \pi_0=\frac{bc}{ab+bc+ca},\qquad
  \pi_1=\frac{ca}{ab+bc+ca},\qquad
  \pi_2=\frac{ab}{ab+bc+ca}.
\]
The stationary flow around every edge is equal: π0a=π1b=π2c=abc/(ab+bc+ca). Unless rates satisfy a special relation, detailed balance fails because the reverse cycle edges have rate zero. The tree formula still gives the stationary law.

This is a useful formal example because each tree sum has one term and normalization is a short positivity argument. It also catches a common orientation error: if one reverses the parent edges, the weights become the wrong products and fail the stationary equation.

## 5. Worked example: a reversible path

Consider \(0\to1\) at rate a, \(1\to0\) at rate b, \(1\to2\) at rate c, and \(2\to1\) at rate d, with all rates positive. The rooted trees have weights
\[
  \tau_0=bd,\qquad \tau_1=ad,\qquad \tau_2=ac.
\]
After normalization these are the stationary masses. The local detailed-balance ratios agree: π0a=π1b and π1c=π2d. The tree formula therefore recovers the birth–death recursion from Chapter 63, but it does not require us to solve that recursion first.

For an undirected path with symmetric edge conductances, every directed tree toward a root has a unique orientation: each edge points along the path toward the root. Thus the tree product is the product of all edge rates, independent of the root, and the stationary distribution is uniform when rates are symmetric. If rates differ by direction but obey detailed balance, the tree sums encode the same reversible weights through products along paths.

For a fully connected three-state chain, write the six directed rates as
\[
  q_{01}=a,\ q_{02}=b,\ q_{10}=c,\ q_{12}=d,\ q_{20}=e,\ q_{21}=f.
\]
Listing the three trees for each root gives
\[
  \tau_0=ce+cf+de,\qquad
  \tau_1=af+ae+bf,\qquad
  \tau_2=bd+ad+bc.
\]
Each monomial corresponds to a different way for the other two states to reach the root. For example, the term de in τ0 uses 1→2 and 2→0; cf uses 1→0 and 2→1. Positivity of all six rates makes every root weight positive. Substituting the τ values into τQ=0 verifies the formula by polynomial cancellation, an ideal `ring`/`nlinarith` exercise after the rate nonnegativity assumptions are set up.

This example also illustrates why tree sums are not usually a compact hand computation: even with three states there are nine monomials across the roots, and the count grows rapidly. The determinant is the efficient compressed representation, while the explicit tree sum is the explanatory combinatorial representation. A good formal library can expose both through an equality theorem and use whichever form suits the downstream proof.

As a symmetric check, give every directed edge of the complete graph on n states the same rate r>0. For each root, a rooted directed tree is an ordinary labeled spanning tree with all edges oriented toward that root. Cayley’s formula counts \(n^{n-2}\) such trees for \(n\geq2\), each of weight \(r^{n-1}\). Thus every τ_r is \(n^{n-2}r^{n-1}\), and the stationary law is uniform. The count is optional for the stationary conclusion—permutation symmetry already gives equal tree sums—but it confirms the scale and demonstrates how a classical combinatorial theorem can feed directly into the tree formula.

## 6. The theorem without reversibility

Detailed balance pairs each transition with its reverse and is an excellent tool when available. The tree theorem instead balances all directed routes into each root. It applies to any finite irreducible generator, including systems with nonzero circulation, directed cycles, and external forcing.

One interpretation is that τ_r measures the total weight of all ways the network can funnel toward r. A state receives stationary mass proportional to its aggregate inward-tree weight. The formula is not merely a local product rule; it sums a global family of spanning structures. For a dense state graph, the number of trees is enormous, but the determinant computes the sum compactly.

For reducible chains, the cofactors can vanish for states outside closed classes, and the normalized tree formula over all states may fail. One must first restrict to a closed irreducible class or analyze the recurrent classes and transient states separately. State irreducibility in the main theorem rather than burying it in a positivity lemma.

## 7. Formalizing rooted arborescences

On a finite type S, a parent assignment can be represented by a function from the nonroot subtype to S. The tree condition says that iteration of this parent map reaches r from every vertex. An alternative is a finite edge set with acyclicity and a unique path to the root. Parent functions make the product weight easy to define; subgraphs make connectivity and spanning-tree lemmas easier to reuse.

The directed rate graph is not exactly Mathlib’s `SimpleGraph`, which is symmetric and irreflexive. A practical design uses a simple graph for the underlying adjacency support and a separate rate function for directed weights. Strong connectivity belongs to the directed relation, while finiteness and undirected spanning-tree facts may use the underlying graph. Do not force a directed rate object into a symmetric graph structure.

Useful intermediate theorems include:

1. a rooted tree has exactly one outgoing parent edge at each nonroot vertex;
2. every nonroot vertex reaches the root after finitely many parent steps;
3. the product weight is nonnegative and positive when all selected rates are positive;
4. the cofactor expansion equals the sum over rooted trees;
5. the vector of cofactors lies in the left kernel of Q;
6. irreducibility makes the normalized left-kernel vector unique.

There is a useful alternative to proving uniqueness by a separate stationary-distribution theorem. Let τ be the positive cofactor vector. Show directly that τQ=0, normalize it, and invoke the finite-chain uniqueness theorem already proved in the Markov-chain part of the book. The tree expansion itself need not establish uniqueness. This keeps the determinant proof focused and reuses established probabilistic structure.

For the rank step in the adjugate proof, a maximum-principle argument can be more transparent than manipulating eigenvalues. If Lf=0, then each f(i) is a rate-weighted average of its out-neighbors. A point of maximum propagates that value along every positive-rate edge; strong connectivity forces f constant. Hence the right kernel has dimension one. Rank-nullity supplies rank |S|−1, and the adjugate columns lie in this one-dimensional kernel. This route exposes the exact role of irreducibility and avoids assuming diagonalizability.

When S is represented by `Fin n`, deleting a root index requires a reindexing of the complement to `Fin (n-1)`. A subtype `{i : Fin n // i ≠ r}` avoids this reindexing but may complicate determinant lemmas. Define a reusable equivalence between the subtype and a finite type with the root removed, and prove the determinant invariant under the induced row and column permutations. For small theorem statements, it is often cleaner to define the principal minor abstractly as a determinant on the complement subtype.

This breakdown keeps permutation signs and tree recursion out of the stationary uniqueness proof. It also allows the determinant theorem to be tested on small finite types using `decide`, `norm_num`, or determinant expansion before the abstract induction is complete.

## 8. A proof-dependency diagram

```text
directed rates ──> rooted-tree weights ──> Laplacian cofactors
                                               │
                                               v
                                          adjugate identity
                                               │
                                               v
                                  positive stationary vector
                                               │
                                               v
                                    normalization + uniqueness
```

The combinatorial theorem is the only step that knows about trees. The linear-algebra tail uses generic finite matrix results. This split is especially valuable in Lean, where a custom proof about directed trees can be substantial but should not be repeated for each chain model.

## 9. Common failure modes

### Root orientation is reversed

The row-Laplacian cofactor counts edges directed toward the deleted root. Check the two-state case.

### A stationary vector is normalized before positivity is proved

Show every rooted tree sum is positive under strong connectivity, then divide by their finite sum.

### Reversibility is assumed unnecessarily

The theorem applies to irreducible directed chains. Requiring detailed balance would exclude the oriented-cycle example.

### Cofactors are confused with arbitrary minors

Use the principal minor deleting both the root row and root column for the corresponding tree sum.

### A reducible chain is treated as having one canonical stationary law

Restrict to a closed irreducible class or describe the recurrent-class decomposition.

## 10. Exercises

1. Compute the tree weights for a two-state chain and recover its stationary law.
2. Verify the oriented three-cycle formula directly from πQ=0.
3. List all rooted trees for a complete directed graph on three vertices with arbitrary positive rates.
4. Prove that strong connectivity gives a positive-weight arborescence for every root.
5. State the cofactor identity using the row Laplacian and prove it for a three-state example.
6. Derive the stationary vector from the adjugate identities and rank (n-1).
7. Show that the tree formula reduces to equal stationary masses on a symmetric directed cycle.
8. Explain how zero transition rates affect the tree sums in a reducible chain.
9. Design a Lean representation of parent assignments and the root-reaching condition.
10. Compare the tree formula with detailed balance on a birth–death path.

## Summary

For a finite irreducible continuous-time chain, each stationary weight is proportional to the sum of products of rates over directed spanning trees pointing toward that state. The directed matrix-tree theorem identifies these sums with principal cofactors of the row Laplacian. The adjugate then places the cofactor vector in the left kernel of the generator, and normalization gives the unique stationary law. Unlike detailed balance, the formula works for nonreversible chains. A Lean development should isolate rooted-tree combinatorics from determinant and nullspace arguments.

## Further reading

- Chapters 45, 63, and 65 for reversible laws, birth–death recurrences, and graph Laplacians.
- [Mathlib’s matrix adjugate documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Adjugate.html).
- [Mathlib’s determinant documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html).
- [Mathlib’s finite spanning-tree and acyclicity results](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Acyclic.html).
