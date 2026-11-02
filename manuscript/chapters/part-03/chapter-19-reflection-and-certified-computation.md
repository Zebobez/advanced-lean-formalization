# Chapter 19 — Reflection and Certified Computation

> **Audience.** This chapter assumes familiarity with Lean's kernel-checked proof terms and the standard arithmetic tactics. It explains when closed computation can prove a proposition, how reflective tactics reduce symbolic goals, and how to account for the trust boundary of compiled evaluation.

Formal proofs often contain calculations that are easy to perform but tedious to justify one step at a time. Lean offers several approaches. A proposition with a computable decision procedure can be evaluated. A specialized tactic can translate a symbolic expression into a simpler representation, compute on that representation, and construct a proof that the computation answers the original question. The key distinction is whether the result is accompanied by evidence that the computation corresponds to the proposition being proved.

## Learning objectives

By the end of this chapter, you should be able to:

- decide when a closed proposition is suitable for `decide`;
- distinguish kernel reduction from native compiled evaluation;
- describe the phases of a reflective proof;
- choose a domain-specific procedure such as `ring`, `norm_num`, or `omega`;
- audit the axioms and trust assumptions of computational proofs.

## 1. Computation can settle closed propositions

Lean can synthesize a `Decidable p` instance for many propositions `p`. A decidable proposition carries enough information to determine whether it is true or false. For a closed goal, `decide` computes that decision and uses the positive result as a proof.

```lean
example : 23 + 19 = 42 := by
  decide

example : 2 + 3 = 5 ∧ 10 < 20 := by
  decide
```

These are proof-producing evaluations. The tactic asks Lean to compute a Boolean decision for the proposition. If the result is true, Lean turns that result into a term proving the proposition. If the result is false, the tactic cannot close the goal. This makes `decide` a natural tool for propositions over finite data, concrete computations, and small decidable relations.

The tactic's default mode does not accept a target containing local variables or metavariables. For example, the goal `n + 0 = n` with arbitrary `n` is true, but its proof is not obtained by evaluating `n` to a numeral. Use a theorem such as `Nat.add_zero` or `simp` instead. The `+revert` option can revert relevant local variables before deciding the resulting proposition. This is useful only when that proposition itself has a tractable `Decidable` instance, as can happen for finite domains; it does not make a general infinite universal statement computable.

The distinction between “there is a decision procedure” and “this decision procedure can be evaluated here” is important. Lean's class `Decidable p` is a piece of data with cases for proving `p` or proving its negation. Some instances compute by recursion over finite data. Others can be introduced classically, where choosing a side is mathematically valid but not computationally reducible. If a goal is classical, adding `classical` may supply a `Decidable` instance without giving `decide` a reduction path. The tactic needs a procedure whose result can actually be computed, not merely the abstract fact that classical logic decides propositions.

This is why a proof by `decide` can depend on the instance Lean synthesized. If a local noncanonical `Decidable` instance is active, it can affect what is being reduced. When a closed computational proof behaves unexpectedly, inspect the proposition's instance and the surrounding classical context, just as you would inspect a typeclass instance for an algebraic operation.

```text
closed proposition p
        │ synthesize Decidable p
        ▼
compute decision ─── false → goal remains
        │ true
        ▼
extract proof term for p
```

The shape of the target matters. A closed arithmetic fact is a better fit for computation than a theorem with arbitrary parameters or a goal whose truth depends on a non-computable mathematical choice.

## 2. Kernel reduction and native evaluation

In its ordinary mode, `decide` reduces the synthesized decision procedure using Lean's definitional reduction. The resulting proof term is checked by the kernel. If the reduction is too expensive, current Lean also provides configuration options such as `decide +kernel` and `decide +native`.

`decide +kernel` uses the kernel's evaluator for reduction. It can unfold definitions more aggressively and can be useful when ordinary elaborator reduction is stuck on transparency. It still produces a proof checked by the kernel. It does not make an undecidable problem decidable; it changes how the computable decision procedure is evaluated.

`decide +native`, also available as `native_decide`, evaluates the decision procedure using compiled native code. This can be substantially faster for large computations, but it changes the trust story. Lean records an axiom for the result; the proof depends on the compiler and the definitions that the runtime executes. Inspect `#print axioms` when using native evaluation in a development where the trusted base matters. The reference documents this tradeoff and the exact modes supported by the current version of Lean.

```lean
example : (List.range 1000).length = 1000 := by
  native_decide
```

This is a suitable kind of task for native evaluation: construct a concrete list and compute its length. It would be a poor use of native computation to prove a general theorem about every list. An induction or a library lemma can establish that theorem without evaluating one enormous closed example.

The choice is not merely about runtime. It is about the proof's dependency boundary. A small result checked by kernel reduction has a different trust profile from a result admitted through compiled evaluation. Both may be useful, but the choice should be visible and deliberate.

## 3. Computation versus proof by reflection

Closed computation evaluates the proposition itself. Reflection is a broader technique: a tactic translates a symbolic expression into a simpler data structure, performs computation on that representation, and uses a correctness theorem to transfer the computed result back to the original expression.

```text
symbolic goal
     │ reify: syntax / expression → data representation
     ▼
normalized representation
     │ verified computation or certificate check
     ▼
proof about the representation
     │ soundness theorem
     ▼
proof of the original goal
```

For a polynomial identity, a reflective tactic can represent the expression as a polynomial, normalize it to a canonical form, compare the normalized forms, and reconstruct a proof from the normalization theorem. The tactic never needs to search for a sequence of rewrites in the original expression. The mathematical soundness comes from the theorem connecting the representation and the expression.

Lean users encounter this pattern through specialized tactics. `ring` handles identities in appropriate algebraic structures, `norm_num` simplifies concrete numerical expressions, and `omega` decides many Presburger arithmetic goals. Their tactics can reason about symbolic variables because they do not need to assign a numerical value to each variable. They compute on a representation of the variables and operations, then justify the result.

```lean
example (x y : ℤ) : (x + y)^2 = x^2 + 2 * x * y + y^2 := by
  ring

example (m n : ℕ) (h : m ≤ n) : m + 1 ≤ n + 1 := by
  omega
```

The choice of tactic encodes a domain boundary. `ring` is suitable when the goal follows from ring identities and the assumptions express the needed algebraic context. It will not prove an inequality requiring an order argument. `omega` handles linear arithmetic in supported number systems, but it will not prove a nonlinear multiplication identity merely because the expression contains numerals. `norm_num` evaluates concrete numeric pieces, but it does not discover the general theorem behind a pattern.

## 4. Boolean computation and propositions

Lean distinguishes a Boolean value from a proposition. A Boolean predicate returns `true` or `false` as data. A proposition states a claim that may be proved or refuted. The expression `decide p` converts a proposition with a `Decidable` instance into a Boolean, but the Boolean result becomes useful for theorem proving only through a connection theorem.

For `decide`, the standard bridge says that obtaining `true` is equivalent to the proposition. At the tactic level, `decide` uses this bridge to extract a proof from computation. For domain-specific Boolean functions, a library theorem usually supplies a specification such as “the Boolean test returns true exactly when the mathematical predicate holds.” That specification is part of the API: clients should use the theorem rather than unfold the implementation of the test.

This separation is essential when formalizing algorithms. Suppose a program computes whether a finite object satisfies a property. A theorem about the program's output needs a correctness statement relating the Boolean result to the mathematical predicate. Testing many examples checks only particular executions; a specification theorem covers all inputs. In reflection, the correspondence between the reified expression and its meaning plays the same role.

Do not confuse `rfl` with a general semantic proof. If a closed Boolean expression reduces definitionally to `true`, reflexivity can establish its equality to `true`. But if the Boolean predicate is defined through a non-reducible algorithm or a different representation, the bridge theorem may require a separate proof. Keep the Boolean implementation and its mathematical specification distinct.

## 5. Certificates separate search from checking

Reflective methods can be organized around a certificate. A potentially sophisticated procedure searches for an answer or a witness; a smaller checker verifies that the certificate is valid. This architecture is useful because the checker can be simple enough to trust and fast enough to run inside the proof system.

In a polynomial identity, the normalization computation can act as the certificate that both expressions have the same normal form. For a propositional tautology, a truth assignment table or a resolution proof can be checked by a small proof-producing procedure. For a finite graph property, the certificate might be a path, coloring, matching, or bounded list of cases. In every instance, there are two logically separate claims:

1. the computation found a certificate;
2. a correctness theorem shows that any accepted certificate implies the original proposition.

If the tactic returns an unchecked Boolean result, the second claim is missing. The tactic might be buggy, the representation might lose information, or the translation might not preserve the intended semantics. Proof-producing reflection keeps these obligations explicit.

The kernel need not rerun the expensive search. It checks the resulting proof term or certificate according to the tactic's design. This explains why a reflective tactic can be efficient and trustworthy at the same time, while a standalone program that merely prints “true” is not by itself a proof.

## 6. Reification and normalization design

When implementing a reflective procedure, reification is often the most delicate step. It should recognize the intended syntax without confusing operations that merely print similarly. In Lean, notation can elaborate to different functions depending on typeclass instances. Addition on naturals and addition on matrices share a symbol but do not share the same semantics.

A robust reifier should therefore inspect elaborated expressions and their types, not just compare surface text. It can map recognized operations to constructors in an expression language:

```text
source expressions       reflected language
──────────────────       ──────────────────
numeral                  literal
variable                 variable identifier
addition                 add node
multiplication           multiply node
power by numeral         power node
```

The evaluator or normalizer operates on this small language. Its soundness theorem says how each constructor denotes a source-level expression. Proving this theorem by structural induction gives the bridge needed to justify normalization.

Normalization itself must terminate and produce a canonical result for the chosen theory. For commutative polynomials, a fixed monomial ordering helps ensure equivalent expressions have identical normalized forms. For arithmetic with inequalities, the representation and decision procedure must preserve strictness, casts, and the arithmetic domain. A tactic author should reduce scope before attempting a general procedure: support a well-defined subset, report when a form is unsupported, and grow the language as the correctness argument grows.

## 7. When computation is the wrong tool

Computational proof is powerful when the proposition is decidable and the relevant data is small or has a compact symbolic representation. It can be inefficient or inappropriate in several common situations.

### A general theorem is disguised as a large closed example

If a result holds by a simple induction, do not compute thousands of cases merely because a native evaluator can finish. State the invariant and prove it once. The induction scales to every input and communicates why the result holds.

### The computation unfolds a large recursive definition

A decision procedure may spend most of its time reducing a program whose behavior is already characterized by useful theorems. Rewrite using those theorems or prove a property of the function abstractly. Computation should not replace a good interface lemma.

### The target is outside the procedure's theory

`ring` does not solve arbitrary inequalities; `omega` does not solve nonlinear Diophantine problems in general; `decide` cannot make an undecidable proposition decidable. Restructure the proof or use a theorem matching the mathematical content.

### Native execution enters the trust boundary unexpectedly

Use `#print axioms` to inspect theorem dependencies. If compiled evaluation is disallowed by the development's trust policy, use a kernel-checked method, a proof-producing tactic, or a theorem that avoids the computation.

## 8. Choosing among common computational tactics

Use `decide` for a concrete proposition with an available decidable instance whose reduction is tractable. Use `native_decide` only when the computation is large enough to justify compiled evaluation and the trust assumptions are acceptable. Use `norm_num` to normalize concrete numeric expressions inside a larger symbolic theorem. Use `ring` for polynomial identities and `omega` for supported linear arithmetic.

These tactics can work together. A proof may use `norm_num` to simplify constants, `ring` to normalize a polynomial identity, and direct lemmas to handle the mathematical structure that neither tactic models. If the same reflective step repeats, factor it into a helper theorem. This gives maintainers a named boundary that can be repaired if tactic behavior or the expression changes.

The desired proof is not necessarily the one with the fewest tokens. It is the one whose tactic choice states the theory being used, whose hypotheses are visible, and whose trust assumptions are appropriate for the result.

## 9. Exercises

1. Prove several closed propositions over `Nat` with `decide`. Then replace one proof with a library theorem and explain which scales better to a variable input.
2. Apply `ring` to a polynomial identity with variables. Identify the reified expression language that a proof-producing implementation would need.
3. Use `norm_num` to discharge a concrete arithmetic subgoal inside a theorem that still has symbolic variables. Separate the concrete and symbolic parts of the reasoning.
4. Compare `decide` and `native_decide` on a closed finite computation. Use `#print axioms` to inspect the resulting dependency difference.
5. Design a small reflected language for expressions built from numerals, variables, addition, and multiplication. State its denotation function and write the soundness theorem you would need before accepting a normalization result.
6. Give an example of a theorem that should be proved by induction rather than by computing many instances. Explain the invariant that makes the inductive proof scalable.
7. Choose a goal and classify it as finite decision, concrete normalization, polynomial identity, linear arithmetic, or structural proof. Defend the tactic choice and state its limitations.

## Summary

`decide` evaluates closed propositions through a synthesized `Decidable` instance. Kernel reduction keeps computation inside the kernel's proof-checking boundary; native evaluation can be faster but adds trust assumptions that should be audited with `#print axioms`. Reflective tactics reify symbolic terms, compute on a representation, and use correctness theorems or certificates to prove the original goal. Match the tactic to its mathematical theory, and use induction or library lemmas when a general argument is clearer than large computation.

## Further reading

- [Lean reference: Decision Procedures](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference)
- [Lean reference: Decidable Propositions](https://lean-lang.org/doc/reference/latest/Type-Classes/)
- [Lean reference: `native_decide` trust boundary](https://lean-lang.org/doc/api/Lean/Meta/Native.html)
- [Mathlib documentation: `norm_num`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormNum/Core.html)
