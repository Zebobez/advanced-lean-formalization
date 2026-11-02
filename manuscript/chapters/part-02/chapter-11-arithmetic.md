# Chapter 11 — Arithmetic and Decision Procedures

> **Audience.** This chapter assumes you know how to state arithmetic propositions and use basic rewriting. It focuses on selecting the right arithmetic tool, understanding its boundary, and keeping automated proofs readable.

Arithmetic goals range from evaluating a numeral to proving a polynomial identity or combining many inequalities. No single tactic handles every kind of arithmetic. Lean and Mathlib provide specialized procedures whose strengths are easier to use when the goal is first classified correctly.

The central decision is whether the proof is about concrete computation, linear order constraints, or algebraic normalization. `norm_num`, `omega`, and `ring` serve different purposes. A named theorem may be clearer than any tactic when it expresses the exact mathematical step.

## Learning objectives

By the end of the chapter, you should be able to:

- use `norm_num` for concrete numeral calculations;
- use `omega` for linear arithmetic over natural numbers and integers;
- use `ring` for polynomial identities in commutative semirings and rings;
- recognize goals that fall outside a tactic's decision procedure;
- handle natural subtraction, coercions, and nonlinear expressions deliberately;
- choose direct library lemmas when they communicate the proof better.

namespace Chapter11

## 1. Classify the goal before choosing a tactic

Arithmetic proof automation works best when the goal is expressed in the language the tactic understands. Begin by asking:

1. Are all quantities concrete numerals?
2. Is the claim a combination of linear equalities, inequalities, addition, subtraction, and constant multiplication?
3. Is it a polynomial identity in a commutative algebraic structure?
4. Does the proof depend on a domain condition such as positivity or nonzero denominator?
5. Is there already a theorem that states exactly what is needed?

The tool choice usually follows:

| Goal shape | First tool to consider |
| --- | --- |
| Closed numerical calculation | `norm_num` |
| Linear `Nat` or `Int` constraints | `omega` |
| Polynomial equality in a commutative ring or semiring | `ring` |
| Linear inequalities over ordered fields | `linarith` |
| A known structural fact in the library | The named theorem |

This classification is more effective than trying every arithmetic tactic in sequence. A tactic that cannot reason about the form of the goal will not become suitable just because the tactic script is longer.

The classification may also suggest a better statement. A closed numerical fact belongs in a `norm_num` example; a universally quantified law should usually expose its algebraic assumptions; and a bound involving natural subtraction should state the ordering hypothesis that makes the subtraction behave as intended. When the theorem's type reflects the mathematical structure, the tactic can remain a small final step instead of carrying the whole proof design.

## 2. Concrete arithmetic with `norm_num`

`norm_num` evaluates numerical expressions and can prove propositions whose truth follows from concrete numerical computation:

```lean
example : (37 : Nat) % 5 = 2 := by
  norm_num

example : (3 : Int) ^ 4 - 5 = 76 := by
  norm_num
```

The tactic also simplifies numerical comparisons and divisibility statements. It is useful for checking a particular boundary case, reducing a closed expression, or finishing the numerical portion of a proof after a general argument has established the needed hypotheses.

For decidable propositions on small finite data, `decide` is another option: it reduces the proposition's decision procedure and returns the resulting proof. `norm_num` is more specialized to numerical expressions and often produces a readable normalization path. Choose based on the form and size of the computation; a proof that works by exhaustive reduction may become expensive as the finite input grows.

It is not a substitute for a theorem about arbitrary variables. For example, calculating `3 * 7` does not establish `3 * n = n + n + n` for every `n`. That statement is algebraic and is better handled with `ring` or a direct theorem. A numeral tactic should be applied to numerals, not expected to invent a general argument.

`norm_num` can also simplify hypotheses. This is useful when a concrete condition remains in the context after a case split. When using it at a hypothesis, inspect the resulting type: the proof may have become `True`, `False`, or a simpler comparison, and the rest of the argument should use that information directly.

## 3. Linear arithmetic with `omega`

`omega` handles many quantifier-free arithmetic goals over `Nat` and `Int`. It combines equalities, inequalities, addition, natural subtraction, multiplication by numerals, and division or remainder by numeral constants. A typical use is to discharge several constraints at once:

```lean
example (n m : Nat) (h₁ : n ≤ m) (h₂ : m < n + 4) : m - n < 4 := by
  omega
```

Here `n ≤ m` ensures that natural subtraction measures the actual gap from `n` to `m`; the upper bound then shows that this gap is less than four. More generally, `omega` can reason with hypotheses, normalize arithmetic expressions, and infer intermediate bounds that would otherwise require several applications of transitivity. It is especially useful for bounds, indices, termination obligations, and small Presburger-arithmetic arguments.

Natural subtraction deserves care. In `Nat`, `a - b` is truncated at zero rather than behaving like integer subtraction. A goal involving `a - b` may depend on whether `b ≤ a`. `omega` can often split or infer the relevant cases, but the mathematical proof should still identify which branch is intended. Sometimes an explicit bound makes the statement and the tactic's input clearer:

```lean
example (a b : Nat) (h : a ≤ b) : a + (b - a) = b := by
  omega
```

The hypothesis is not decoration: it ensures the subtraction is operating in the nontruncated case.

### The boundary of linear arithmetic

`omega` does not prove arbitrary nonlinear facts such as distributivity with products of variables or multiplicative growth estimates. It can handle `7 * n` because 7 is a constant coefficient; it cannot generally solve a statement whose essential content depends on the product `n * m` of two variables.

It also does not reason in all ordered numeric types. For rational and real inequalities, `linarith` is often suitable when the expressions are linear. For polynomial identities over any suitable commutative semiring or ring, `ring` is usually the right tool. If a proposition involves square roots, exponentials, or division by an expression, first state and prove the domain facts those operations require.

## 4. Polynomial identities with `ring`

The `ring` tactic proves identities that follow from the axioms of a commutative ring or semiring by normalizing both sides to a common polynomial form:

```lean
example (x y : Int) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
```

The tactic handles associativity, commutativity, distributivity, and powers with natural exponents. It is valuable when a proof is algebraically routine but expanding and collecting terms by hand would obscure the point.

The domain matters. In a ring, subtraction and negation are included. In a semiring such as `Nat`, subtraction is not a ring operation, so a polynomial identity using subtraction may need a different statement or a different type. Coercions should be visible enough that Lean knows which algebraic structure the expressions inhabit.

`ring` proves equalities, not arbitrary inequalities or order-theoretic claims. It cannot justify division cancellation without a nonzero hypothesis, and it does not establish positivity. The identity `x / x = 1` is not a ring normalization: it is false at zero and requires a condition that `x` is nonzero in a field. Prove such side conditions separately, then apply the appropriate theorem.

For a polynomial identity mixed with a hypothesis, rewrite by the hypothesis first and then normalize:

```lean
example (a b c : Int) (h : c = b * a + a * b) : c = 2 * a * b := by
  rw [h]
  ring
```

The rewrite makes the relationship between the hypothesis and the target explicit. `ring` then handles only the algebraic normalization. This is often easier to maintain than asking one tactic to solve a goal containing both local assumptions and a substantial identity.

When the goal needs both normalization and arithmetic constraints, separate the stages. Simplify concrete operations and rewrite definitions first; use `ring` for polynomial equality; then use an order solver for the remaining inequalities. This exposes a useful proof boundary and makes it clear which assumptions discharge which part of the theorem.

## 5. Sign goals and linear inequalities

Some arithmetic obligations are about sign rather than exact values. Mathlib's `positivity` tactic can prove many goals whose positivity follows from known signs and nonnegative operations:

```lean
example {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  positivity
```

For linear inequalities over ordered rings or fields, `linarith` combines linear equalities and inequalities from the context. It is often a good choice for rational or real variables, where `omega` does not apply. For nonlinear real inequalities, `nlinarith` can combine polynomial constraints, although nonlinear reasoning may require stronger hypotheses and can be less predictable.

These tactics do not replace each other. `positivity` reasons about signs of expressions; `linarith` derives consequences of linear constraints; `nlinarith` handles selected polynomial relations. If the goal is simply a ring identity, use `ring`. If it requires an order argument over `Nat` or `Int`, begin with `omega` or a named monotonicity theorem.

## 6. Direct lemmas can be better than automation

If a goal is a direct instance of a theorem, using that theorem can produce the clearest proof. For example, monotonicity of successor is a named mathematical fact:

```lean
example {a b : Nat} (h : a ≤ b) : a + 1 ≤ b + 1 := by
  exact Nat.add_le_add_right h 1
```

The tactic `omega` could also prove this. The theorem is preferable when the intent is to apply monotonicity and the proof is short. The tactic is preferable when many arithmetic constraints must be combined or the needed intermediate facts are not obvious.

Direct lemmas also preserve abstraction. A theorem about an ordered algebra may work for many types, while `omega` applies only to its supported numeric domains. A proof that uses the library's general theorem can remain reusable when the concrete representation changes.

An effective proof often has three stages:

```text
rewrite with mathematical hypotheses
             │
             ▼
normalize the algebraic expression
             │
             ▼
discharge the remaining order constraints
```

For example, `rw` can apply a recurrence, `ring` can normalize a polynomial, and `omega` can prove a final natural-number bound. Each tool then handles the part for which it is designed.

## 7. Coercions and mixed numeric types

An arithmetic proof can fail because the expressions inhabit different types. Natural numbers, integers, rationals, and reals have different subtraction, division, and order behavior. Coercions may make an expression look familiar while its elaborated type differs from the expected one.

Before invoking a tactic, inspect the goal and hypotheses. Ask whether a numeral has been inferred as `Nat` or `Int`, whether a coercion is present, and whether subtraction is truncated. A tactic may be perfectly capable of solving the mathematical proposition but not be configured to bridge type conversions automatically.

Use a cast-normalization theorem or tactic such as `norm_cast` when the issue is a legitimate cast. Do not cast everything to a larger type merely to avoid understanding the original proposition; that can erase useful discreteness or introduce extra side conditions. State the argument in the type that best reflects the mathematics, then cast at the interface where the types actually meet.

For instance, an integer inequality may follow from a natural-number inequality after casting, but an integer proof can no longer use a fact that depends on the discreteness of naturals without stating the relevant integral bound. Choose the domain in which the key argument is simplest, and cross between domains at a named boundary. This tends to produce shorter hypotheses and more reusable lemmas.

## 8. Reading failures as information

When a tactic fails, classify the failure instead of immediately trying a different tactic:

- `norm_num` fails on variables: the claim is not a closed calculation.
- `omega` leaves a product of variables: the argument may be nonlinear.
- `ring` leaves an inequality: algebraic normalization is not order reasoning.
- a tactic sees incompatible casts: the numeric domains must be aligned.
- a division identity lacks a hypothesis: add the mathematical nonzero or positivity condition.
- no tactic applies cleanly: search for a library theorem or strengthen the statement.

This diagnosis often points to a better theorem statement. If an estimate needs positivity, include positivity in the hypotheses. If a nonlinear product is bounded using an upper bound on one factor, state that bound explicitly. Automation becomes more predictable when the assumptions describe the structure the proof actually uses.

## 9. Common failure modes

### `omega` is asked to prove a polynomial identity

Use `ring` for commutative polynomial equalities. If order is involved, separate the algebraic simplification from the inequality argument.

### `ring` is asked to prove an inequality

Normalize equality subgoals with `ring`; use `omega`, `linarith`, or a named monotonicity theorem for order. Algebraic normalization does not establish signs.

### `norm_num` is used for a theorem with variables

Use it for concrete numerical computation. For variable expressions, identify the algebraic or order-theoretic structure instead.

### Natural subtraction hides a case condition

Supply or derive the bound that prevents truncation. If the statement should hold in all cases, prove the cases explicitly or formulate the claim over integers.

### Several tactics are piled together without inspecting the goal

Normalize hypotheses and expressions deliberately. Tactic order should reflect the mathematics: simplify known forms, apply relevant equations, then use the decision procedure that matches the remaining goal.

## 10. Exercises

1. Use `norm_num` to prove three closed arithmetic facts, including one remainder calculation.
2. Prove a bound involving `Nat` subtraction with `omega`. State the hypothesis that prevents truncation.
3. Prove a polynomial identity in `Int` with `ring`, then identify why the same tactic would not prove a positivity statement.
4. Combine a rewrite from a hypothesis with `ring` to prove a rearranged algebraic identity.
5. Find an arithmetic goal that `omega` cannot solve because it is nonlinear. Add a useful hypothesis or choose a different tactic.
6. Replace an automated proof with a named monotonicity theorem where that theorem gives a clearer explanation.
7. Take a mixed cast goal from your own development and identify the exact point at which a cast-normalization lemma is needed.

## Summary

Classify arithmetic goals before choosing automation. `norm_num` evaluates concrete numerical expressions; `omega` combines linear arithmetic constraints over natural numbers and integers; `ring` normalizes polynomial equalities in commutative algebraic structures. None replaces domain conditions or arbitrary mathematical reasoning. Use named theorems when they express the step directly, keep casts and subtraction behavior visible, and combine specialized tools in small stages rather than asking one tactic to solve an unrelated mixture of goals.

## Further reading

- [Mathlib tactics reference](https://leanprover-community.github.io/mathlib4_docs/tactics.html)
- [Mathlib `ring` tactic reference](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Ring/Basic.html)
- [Mathlib `norm_num` tactic reference](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormNum/Core.html)
- [Mathematics in Lean: Basics and ring normalization](https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html)

end Chapter11
