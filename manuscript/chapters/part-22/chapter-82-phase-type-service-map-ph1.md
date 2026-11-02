# Chapter 82 — Phase-Type Service and MAP/PH/1 Queues

> **Audience.** This chapter builds on phase-based continuous-time chains, MAP arrivals, and QBDs. It assumes familiarity with finite generators, matrix exponentials, and matrix-geometric stationary laws. The goal is to encode non-exponential service times without losing a Markov state description.

An exponential service time is memoryless, so a queue with exponential service needs only its level and arrival phase as state variables. For a general service-time distribution, the remaining service time matters. A phase-type (PH) distribution restores a finite Markov description by representing service as absorption from a finite transient chain.

This construction makes a MAP/PH/1 queue a QBD. The busy levels carry both the arrival phase and the current service phase; the empty level carries only the arrival phase. That difference gives rectangular boundary blocks, a useful example of how an elegant mathematical model should influence the shape of a formal API.

## Learning objectives

After this chapter, you should be able to:

- define a PH distribution as an absorption time and compute its moments;
- build Erlang and hyperexponential PH representations;
- assemble the interior blocks of a MAP/PH/1 queue using Kronecker products;
- derive the separate idle-boundary blocks and verify their dimensions;
- recover the matrix-geometric equation and the traffic-load condition;
- design Lean types that express the changing phase space at level zero.

## 1. Service as absorption from transient phases

Let \(\mathrm{ServicePhase}\) be a finite type of transient service phases. A PH representation consists of:

- a row probability vector \(\beta\) giving the initial service phase;
- a subgenerator \(T\) on transient phases;
- an absorbing exit-rate column \(t=-T\mathbf 1\).

The off-diagonal entries of \(T\) are nonnegative, and its row sums are nonpositive. Properness requires that absorption occurs with probability one; equivalently in finite dimension, the transient semigroup decays and \(-T\) is invertible. The service time is the time until the CTMC with transient generator \(T\), started from \(\beta\), is absorbed.

For \(x\geq0\), the survival function and density are

\[
\mathbb P(S>x)=\beta e^{Tx}\mathbf 1,\qquad
f_S(x)=\beta e^{Tx}t.
\tag{82.1}
\]

The Laplace transform and moments are

\[
\mathbb E[e^{-sS}]=\beta(sI-T)^{-1}t,\qquad s\geq0,
\tag{82.2}
\]

\[
\mathbb E[S^k]=k!\,\beta(-T)^{-k}\mathbf 1,\qquad k\geq1.
\tag{82.3}
\]

In particular, the mean service time is \(\beta(-T)^{-1}\mathbf1\). These matrix formulas turn questions about a random duration into finite-dimensional linear algebra.

The PH class includes many common distributions exactly and can approximate a broad range of positive-valued service laws. Approximation is a modeling step, not a theorem that the chosen PH representation equals an arbitrary service distribution. A formal development should keep the fitted model and any approximation error analysis separate.

## 2. Two useful PH representations

### 2.1 Erlang service as sequential stages

An Erlang-2 service time with stage rate \(\nu\) is the sum of two independent exponential stages. Its representation is

\[
\beta=(1,0),\qquad
T=\begin{pmatrix}-\nu&\nu\\0&-\nu\end{pmatrix},\qquad
t=\begin{pmatrix}0\\\nu\end{pmatrix}.
\]

Absorption is possible only after the second stage. From (82.3),

\[
\mathbb E[S]=\frac{2}{\nu},\qquad
\mathbb E[S^2]=\frac{6}{\nu^2},\qquad
\operatorname{Var}(S)=\frac{2}{\nu^2}.
\]

The mean service rate is \(\nu/2\), but the service duration is less variable than an exponential time with that same mean.

### 2.2 Hyperexponential service as a mixture

Choose one of two exponential service modes at the start, with probabilities \(p\) and \(1-p\). Then

\[
\beta=(p,1-p),\qquad
T=\begin{pmatrix}-\mu_1&0\\0&-\mu_2\end{pmatrix},\qquad
t=\begin{pmatrix}\mu_1\\\mu_2\end{pmatrix}.
\]

The mean is \(p/\mu_1+(1-p)/\mu_2\), and the second moment is \(2p/\mu_1^2+2(1-p)/\mu_2^2\). A mixture of a fast and a slow mode can produce high variability even when its mean matches an exponential service model.

These examples show why formalizing only the mean is insufficient for queue analysis. Two service laws can have the same mean and different variability, yet the PH representation retains enough structure to compute the effects on stationary tails.

## 3. Representation is not distribution

PH representations are not unique. An Erlang-2 law can be represented with its two successive stages, but an equivalent realization may contain additional transient states. Permuting the phase labels also changes the matrices while leaving the service distribution unchanged.

This distinction matters for API design. A theorem about \(T\) and \(\beta\) proves a statement about a representation. To state a representation-independent result, define the induced probability law or show that a transformation of the phase realization preserves the absorption-time distribution. Do not identify the dimension or labels of the service phases with intrinsic properties of the random variable.

In a Lean library, it is useful to separate:

1. finite matrix data satisfying the subgenerator and initial-probability conditions;
2. the absorption-time distribution induced by that data;
3. derived moments such as \(\beta(-T)^{-1}\mathbf1\);
4. a queue model that consumes the PH representation.

The queue construction should depend on the representation interface, not on a particular Erlang or hyperexponential encoding.

For example, a permutation matrix \(P\) changes only the names and ordering of service phases:

\[
\beta'=\beta P,\qquad T'=P^{-1}TP,\qquad t'=P^{-1}t.
\]

Because \(P\mathbf1=\mathbf1\), the transformed survival expression satisfies
\[
\beta'e^{T'x}\mathbf1=\beta e^{Tx}\mathbf1.
\]

This gives a concrete representation-equivalence lemma. More general reductions may remove unreachable phases or merge states when the required probabilistic equivalence conditions hold, but those transformations need separate proofs; matrix dimension alone does not certify equivalence.

## 4. State space for a MAP/PH/1 queue

Let \((D_0,D_1)\) describe the MAP arrivals on a finite arrival phase set \(\mathrm{ArrivalPhase}\). Write

\[
D=D_0+D_1
\]

for its background generator and \(\alpha D=0\), \(\alpha\mathbf1=1\) for the stationary phase distribution. Arrivals have mean rate

\[
\lambda=\alpha D_1\mathbf1.
\tag{82.4}
\]

The service mechanism is PH with representation \((\beta,T)\) on \(\mathrm{ServicePhase}\), independent of the MAP. When the system is busy, the joint phase is a pair \((i,j)\): arrival phase \(i\), service phase \(j\). The number of busy phases is the product of the two finite cardinalities.

When the system is empty, there is no active service phase. The level-zero phase set is only \(\mathrm{ArrivalPhase}\), whereas every positive level uses \(\mathrm{ArrivalPhase}\times\mathrm{ServicePhase}\). This gives the block pattern

~~~text
                 idle level 0        busy level 1       busy level 2       ...
level 0             B00                  B01                 0
level 1             B10                   A0                 A1
level 2               0                   A-1                A0                A1
level 3               0                    0                 A-1               A0       A1
  ...
~~~

The interior phase dimension is fixed, but the boundary blocks may be rectangular. In particular, \(B_{01}\) maps an arrival phase into an arrival-service pair, and \(B_{10}\) maps a pair back to an arrival phase.

## 5. Deriving the QBD blocks

Use the Kronecker product with arrival phase first and service phase second. Let \(I_a\) and \(I_s\) be the identity matrices on those two spaces. At positive levels, an arrival changes the MAP phase according to \(D_1\) and leaves the service phase unchanged:

\[
A_1=D_1\otimes I_s.
\tag{82.5}
\]

No-arrival MAP transitions and within-service-phase transitions both preserve the level. Their generators add:

\[
A_0=D_0\otimes I_s+I_a\otimes T.
\tag{82.6}
\]

When service completes and at least one customer remains, the next customer begins service with initial distribution \(\beta\). The environment is unchanged, so

\[
A_{-1}=I_a\otimes(t\beta).
\tag{82.7}
\]

At level one, a completion leaves the system empty. There is no new service phase to initialize; the destination is just the arrival phase:

\[
B_{10}=I_a\otimes t.
\tag{82.8}
\]

At level zero, an arrival both triggers service phase initialization and may change the MAP phase:

\[
B_{00}=D_0,\qquad B_{01}=D_1\otimes\beta.
\tag{82.9}
\]

Dimensions make the event logic visible. If there are \(m\) arrival phases and \(q\) service phases, then \(B_{00}\) is \(m\times m\), \(B_{01}\) is \(m\times mq\), \(B_{10}\) is \(mq\times m\), and each interior block is \(mq\times mq\).

## 6. Generator checks and stationary equations

The Kronecker row-sum identity

\[
(U\otimes V)(\mathbf1\otimes\mathbf1)
=(U\mathbf1)\otimes(V\mathbf1)
\]

provides a compact way to verify the full generator. Since \(D_0\mathbf1+D_1\mathbf1=0\), \(T\mathbf1=-t\), and \(\beta\mathbf1=1\), an interior row sums to

\[
(D_1\mathbf1)\otimes\mathbf1
+(D_0\mathbf1)\otimes\mathbf1-\mathbf1\otimes t
+\mathbf1\otimes t=0.
\]

At level zero, \(B_{00}\mathbf1+B_{01}(\mathbf1\otimes\mathbf1)=D_0\mathbf1+D_1\mathbf1=0\). For a level-one row, the rate into level zero through \(B_{10}\) supplies exactly the absorption rate \(t\) removed by \(I_a\otimes T\). Nonnegative off-diagonal rates follow from the MAP and PH conditions.

Let \(\pi_0\) be the row of idle-level masses and \(\pi_n\) the row of busy-level masses. The boundary balance equations are

\[
\pi_0B_{00}+\pi_1B_{10}=0,
\tag{82.10}
\]

\[
\pi_0B_{01}+\pi_1A_0+\pi_2A_{-1}=0.
\tag{82.11}
\]

For \(n\geq2\), the repeated interior recurrence is

\[
\pi_{n-1}A_1+\pi_nA_0+\pi_{n+1}A_{-1}=0.
\tag{82.12}
\]

With \(\pi_n=\pi_1R^{n-1}\), the rate matrix has dimension \(mq\times mq\) and solves

\[
A_1+RA_0+R^2A_{-1}=0.
\tag{82.13}
\]

When \(\rho(R)<1\), normalization is

\[
\pi_0\mathbf1_m+\pi_1(I-R)^{-1}\mathbf1_{mq}=1.
\tag{82.14}
\]

The boundary and interior phase spaces differ, but the matrix-geometric tail remains intact once the system is in its repeating busy region.

## 7. Stability from arrival rate and service mean

The MAP has long-run arrival rate \(\lambda=\alpha D_1\mathbf1\), and one service requirement has mean

\[
m_S=\beta(-T)^{-1}\mathbf1.
\]

For an irreducible MAP/PH/1 queue with independent, identically distributed service times and the usual finite-state regularity assumptions, the traffic intensity is

\[
\rho=\lambda m_S.
\tag{82.15}
\]

Positive recurrence holds when \(\rho<1\). This is a useful reduction: arrival correlation affects the stationary distribution and its tail, but the stability test uses the MAP's long-run mean rate and the PH service mean. A mean-rate condition does not imply that the stationary queue distribution equals the M/M/1 geometric law.

When \(\rho\geq1\), a normalized stationary distribution for the infinite-buffer single-server queue does not exist under these assumptions. A finite buffer changes the model and can remain positive recurrent, but then overflow and blocking transitions require a different upper boundary.

## 8. Worked example: two-state MMPP with Erlang-2 service

Take the two-state MMPP from Chapter 81 with switching rates \(a=1\), \(b=2\), and arrival rates \(\lambda_0=1/2\), \(\lambda_1=2\). Its stationary phase distribution is \(\alpha=(2/3,1/3)\), so the mean arrival rate is \(\lambda=1\).

Let service be Erlang-2 with stage rate \(\nu=3\):

\[
\beta=(1,0),\qquad
T=\begin{pmatrix}-3&3\\0&-3\end{pmatrix},\qquad
t=\begin{pmatrix}0\\3\end{pmatrix}.
\]

The mean service time is \(2/3\), giving \(\rho=2/3<1\). There are two arrival phases, two service phases, and four busy phases. With

\[
D_0=\begin{pmatrix}-3/2&1\\2&-4\end{pmatrix},
\qquad
D_1=\begin{pmatrix}1/2&0\\0&2\end{pmatrix},
\]

the boundary blocks are

\[
B_{00}=D_0,\qquad B_{01}=D_1\otimes\beta,\qquad B_{10}=I_2\otimes t,
\]

and the repeating blocks are

\[
A_1=D_1\otimes I_2,\quad
A_0=D_0\otimes I_2+I_2\otimes T,\quad
A_{-1}=I_2\otimes(t\beta).
\]

This example shows the reset mechanism at completion. At level two or above, service completion moves to the next lower level and draws a fresh service phase from \(\beta\). At level one, completion moves to the idle boundary and no service phase is drawn. A generator check that uses \(I_2\otimes(t\beta)\) for the level-one-to-zero block would have the wrong number of columns and would encode the wrong state space.

## 9. Lean formalization strategy

Use distinct finite types for arrival and service phases. Represent \(D_0,D_1,T,\beta,t\) with their source and destination indices explicit. A PH data structure should carry proofs that \(\beta\) is a probability vector, off-diagonal entries of \(T\) are nonnegative, \(t=-T\mathbf1\) is nonnegative, and absorption is proper. A MAP structure should carry its own row-sum and sign conditions.

The MAP/PH/1 constructor then proves:

1. the dimensions of the Kronecker blocks;
2. the generator row sums at the idle boundary, level one, and all higher levels;
3. nonnegativity of off-diagonal rates;
4. equivalence of each block balance equation to the corresponding full-state balance equations;
5. the substitution of (82.5)–(82.7) into the generic QBD rate-matrix theorem.

The boundary matrices are rectangular, so do not force \(B_{00}\), \(B_{01}\), and \(B_{10}\) into a single square-matrix type. Use matrix types indexed by the actual source and destination phase types. A state encoding can use a dependent phase type by level, or a structure with an optional service phase and an invariant saying that it is absent exactly when the level is zero. The second encoding may simplify user-facing definitions; the first can make the generator block decomposition more direct.

The critical algebraic lemmas are small and reusable. For Kronecker products, prove the row-sum identity and the action on tensor-product vectors once. For PH data, prove the absorption vector formula and the mean expression once. The queue development should assemble those lemmas rather than re-prove matrix exponential facts in every example.

## 10. Common failure modes

1. **Treating the service phase as active while idle.** No job is in service at level zero, so the boundary phase dimension is smaller.
2. **Failing to reset service after a completion.** At levels \(n\geq2\), a fresh job starts with distribution \(\beta\); at level one, the system becomes empty instead.
3. **Using the service rate \(1/m_S\) as if service were exponential.** The mean determines the load, but the PH phases determine queue behavior.
4. **Using \(t\) where \(t\beta\) is required.** A busy-to-busy completion resets a phase and needs a square service transition block; a busy-to-idle completion does not.
5. **Ignoring MAP phase changes during arrivals.** \(D_1\) can move the arrival phase and must be tensored with the service identity while busy.
6. **Assuming the PH representation is unique.** Equivalent service distributions may have different phase dimensions and matrices.
7. **Applying one square boundary type to every level.** The idle boundary naturally has rectangular maps to and from the busy phase space.
8. **Confusing mean-load stability with a geometric stationary law.** The condition \(\lambda m_S<1\) gives positive recurrence, while the actual level tail is generally matrix-geometric.

## 11. Exercises

1. **PH moments.** Starting from the Laplace transform in (82.2), derive the mean and second moment in (82.3).
2. **Erlang-3.** Write a three-stage Erlang representation, compute its mean and variance, and compare its squared coefficient of variation with that of an exponential law of the same mean.
3. **Mixture moments.** For the two-mode hyperexponential representation, derive the mean and variance as functions of \(p,\mu_1,\mu_2\).
4. **Block dimensions.** If there are \(m\) MAP phases and \(q\) service phases, state the type of every boundary and interior block and verify that each product in (82.10)–(82.13) is well-typed.
5. **Row sums.** Prove the interior row-sum identity using the Kronecker product identity and \(t=-T\mathbf1\).
6. **Load calculation.** For the MMPP/Erlang-2 example, replace \(a,b,\lambda_0,\lambda_1,\nu\) by positive symbolic parameters and derive \(\rho\).
7. **Lean state representation.** Compare a dependent phase type indexed by level with an optional service-phase field plus a validity invariant. Which gives simpler generator definitions? Which gives simpler block theorems?
8. **Representation changes.** Explain why permuting service phases changes \(T\) and \(\beta\) but not the absorption-time distribution, and outline a matrix conjugacy argument.

## 12. Summary

A PH service time is an absorption time described by an initial row vector \(\beta\), a transient subgenerator \(T\), and exit rates \(t=-T\mathbf1\). Its mean is \(\beta(-T)^{-1}\mathbf1\), and its higher moments are finite matrix expressions.

In a MAP/PH/1 queue, busy phases are arrival-service pairs while idle phases contain only the arrival environment. Kronecker products give the repeating blocks; separate rectangular blocks handle arrivals into an idle system and service completion back to idle. The resulting process is a QBD with stability condition \(\lambda\,\mathbb E[S]<1\) and a matrix-geometric stationary tail.

The Lean development should make the PH and MAP hypotheses explicit, preserve the boundary dimensions, and reuse the generic QBD theorems. The matrix representation carries information about variability that a mean service rate alone cannot retain.

### Further reading

- G. Latouche and V. Ramaswami, [“PH Distributions,” Chapter 2 of *Introduction to Matrix Analytic Methods in Stochastic Modeling*](https://doi.org/10.1137/1.9780898719734.ch2), ASA-SIAM Series on Statistics and Applied Probability, 1999. This chapter develops absorption-time representations and their tractable moment formulas.
- A. Asanjarani and Y. Nazarathy, [“A Queueing Approximation of MMPP/PH/1”](https://doi.org/10.1007/978-3-319-22267-7_4), in *Queueing Theory and Network Applications*, Advances in Intelligent Systems and Computing 383, Springer, 2016. The paper displays the QBD block construction for phase-modulated arrivals and PH service.
- M. F. Neuts, *Matrix-Geometric Solutions in Stochastic Models: An Algorithmic Approach*, Johns Hopkins University Press, 1981.
