# Chapter 10 — Structured Rewriting with `calc` and `conv`

> **Audience.** This chapter assumes you can use `rw`, `simp`, and basic equality reasoning. It develops two tools for proofs that need more structure: `calc` for visible chains of relations and `conv` for rewriting a precisely selected subexpression.

The rewrite tactic is compact, but a long sequence of rewrites can make the mathematical argument hard to see. A calculation turns the proof into a chain of intermediate claims. Conversely, a rewrite may be mathematically correct but hit the wrong occurrence in a large expression. Conversion mode lets the proof navigate to one subterm before changing it.

The goal is not to use more syntax. It is to make each transformation local and its reason visible. `calc` clarifies the sequence of claims; `conv` clarifies where a rewrite occurs.

## Learning objectives

By the end of the chapter, you should be able to:

- write equality and inequality chains with `calc`;
- combine different relations in one transitive calculation;
- choose intermediate expressions that expose the mathematical argument;
- navigate inside an expression with `conv`;
- rewrite under a binder or in one selected occurrence;
- decide when ordinary `rw` or `simp` is clearer than either tool.

The examples are in namespace `Chapter10`.

## 1. A calculation is a chain of typed steps

Suppose a proof has hypotheses `a = b` and `b ≤ c`. A calculation makes the path to the target visible:

```lean
namespace Chapter10

example {a b c : Nat} (h₁ : a = b) (h₂ : b ≤ c) : a ≤ c := by
  calc
    a = b := h₁
    _ ≤ c := h₂
```

Each line has a source expression, a relation, a destination expression, and a proof of that step. The underscore means “the left endpoint from the previous line.” Lean checks that each step can compose with the preceding one. In the example, equality transports the bound from `b` to `a`, then the inequality concludes the result.

A calculation is not restricted to equality. Any relation with suitable transitivity can appear. The relation can change from line to line as long as the steps compose. For example:

```lean
example {a b c d : Nat}
    (hab : a = b) (hbc : b ≤ c) (hcd : c < d) : a < d := by
  calc
    a = b := hab
    _ ≤ c := hbc
    _ < d := hcd
```

This proof communicates three mathematical moves: substitute equals, use a non-strict bound, then finish with a strict bound. A single tactic might solve the same goal, but the calculation preserves the structure of the argument for a reader.

`calc` is term syntax, so it can be the proof of an entire declaration or the term supplied to `exact`. The block does not depend on tactic state: each line is checked as a proof of a relation between two expressions. This makes calculations convenient inside a theorem with several independent arguments, where a local tactic block can obscure which hypothesis justifies which step.

The shape of a calculation also gives Lean information. Each intermediate expression fixes the expected type of the next proof. If a lemma has several implicit parameters, writing the intermediate endpoint often gives the elaborator enough context to infer them. When inference still fails, annotate the endpoint or pass the lemma's arguments explicitly instead of replacing the calculation with a large search tactic.

## 2. Choosing useful intermediate statements

The expressions in a calculation should correspond to meaningful intermediate claims. They are not decoration: each one determines the type Lean expects for the next proof.

For instance, if `a = b`, adding one preserves equality, and a separate hypothesis gives an upper bound:

```lean
example {a b c : Nat} (hab : a = b) (hbc : b ≤ c) :
    a + 1 ≤ c + 1 := by
  calc
    a + 1 = b + 1 := by rw [hab]
    _ ≤ c + 1 := Nat.add_le_add_right hbc 1
```

The first step is an equality; the second is an inequality. Each proof is small because the chain exposes the exact lemma needed at that point.

An intermediate expression can also normalize a representation before applying a theorem. A common strategy is:

```text
original expression
        │ rewrite using definition
        ▼
canonical form
        │ apply a library theorem
        ▼
target expression
```

The chosen normal form should reduce the complexity of the remaining proof. If a calculation introduces irrelevant algebra, the intermediate steps are not helping; combine or remove them.

### Use a named lemma when a step deserves reuse

If the same transition appears in several calculations, give it a name rather than copying its proof. The calculation then reads like a mathematical outline, while each named theorem owns its local details. This is especially useful when the step depends on a nontrivial invariant or library-specific rewrite.

For a one-off step, an inline `by` proof is usually enough. A useful rule is to extract a lemma when it has a clear statement independent of the surrounding calculation, or when the calculation becomes difficult to scan because one line contains a long tactic script.

## 3. Calculations can follow equality rewrites

For equality goals, `calc` can document a sequence of rewrites without hiding them in one long `rw` list:

```lean
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  calc
    a + c = b + c := by rw [h]
```

This example has one step, but the same structure scales to a derivation with several identities. Each equality should explain why the next expression is equivalent to the previous one. If the step is purely definitional, `rfl` may be the clearest proof. If it invokes a theorem, name the theorem or state the reason inline.

Avoid writing a calculation where every line simply restates the previous goal with a different tactic. The proof should expose mathematical transformations, not merely the history of commands used to discover them.

### Relation composition is checked, not assumed

The relation on consecutive lines must be composable. A chain that ends with `a = b` and continues from `c ≤ d` has a gap unless the expression endpoints match or another step connects `b` to `c`. If Lean reports a type mismatch in a `calc` block, compare the previous right endpoint with the next left endpoint first.

Lean can infer omitted relation endpoints in many cases, but explicit expressions are often easier to read in a textbook proof. Use `_` for the repeated endpoint; write the new endpoint and relation that carry the argument forward.

## 4. The rewrite tactic chooses an occurrence

The ordinary `rw` tactic selects a matching subexpression according to its rewrite strategy. On a small expression, this is usually exactly right. On an expression with multiple occurrences, the first matching term may not be the one the proof author had in mind.

Consider the goal:

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    arg 2
    rw [Nat.mul_comm]
```

The first `lhs` selects the left side of the equality. The `arg 2` navigation enters the second explicit argument of the outer multiplication, namely `b * c`. The rewrite now commutes that inner multiplication only. The right side remains untouched, and the resulting sides are definitionally equal.

If we had written `rw [Nat.mul_comm]` at the top level, Lean would first match the outer multiplication and transform `a * (b * c)` into `b * c * a`. That rewrite is valid but irrelevant to the intended proof. `conv` keeps the rewrite local to the selected expression.

## 5. Navigation in conversion mode

Conversion mode has commands for moving through an expression before applying a rewrite:

- `lhs` and `rhs` select the sides of an equality or relation;
- `arg n` enters the `n`th argument of the current expression;
- `congr` creates subgoals for the arguments of the current function application;
- `intro x` enters a function or universal binder;
- `pattern e` navigates to a selected subexpression matching `e`;
- `rw` and `simp` rewrite or simplify the currently selected expression.

For example, rewriting under a lambda abstraction can be done by entering the left side and then the binder:

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]
```

The conversion step enters the body `0 + x`, rewrites it to `x`, and leaves the two lambda expressions equal. In many actual proofs, `funext` followed by `simp` would be shorter. The conversion example demonstrates the navigation facility; use it when a direct rewrite is blocked by a binder or would affect the wrong occurrence.

Conversion mode can target a hypothesis as well as the goal:

```lean
example (h : a + 0 = b) : a = b := by
  conv at h =>
    lhs
    rw [Nat.add_zero]
  exact h
```

Here the left side of `h` is normalized in place. This can make a hypothesis usable without rewriting every occurrence in the goal. For simple changes, `rw [Nat.add_zero] at h` is clearer; use `conv at h` when only a particular nested expression should change.

The same precision helps when an expression contains two related terms and only one should be normalized. In the following example, commutativity is applied to the second summand, after which a ring identity closes the goal:

```lean
example (a b : Nat) : a * b + b * a = 2 * (a * b) := by
  conv =>
    lhs
    arg 2
    rw [Nat.mul_comm]
  ring
```

The conversion step documents the selected occurrence, while `ring` handles the resulting polynomial identity. This division of labor is often effective: use `conv` for syntactic location and a decision procedure for the mathematical normalization.

## 6. Occurrence selection and exact scope

When a target expression contains several copies of the same term, conversion mode makes the scope of a rewrite explicit. One can navigate by arguments or use `pattern` to select a term. The proof then changes that subterm and leaves structurally similar occurrences alone.

This precision is useful in:

- nested arithmetic expressions where a lemma matches both outer and inner operations;
- goals with function applications under lambdas;
- rewriting a specific hypothesis without changing the rest of the context;
- proofs where only one side should be normalized;
- expressions where simplification is valid locally but not desirable globally.

The extra navigation has a cost. A long `conv` path can become brittle if the expression's structure changes. Prefer a named subexpression lemma or a direct rewrite when possible. Use `conv` when locality is part of the proof's intent, not simply because the tactic exists.

## 7. A decision guide

Choose among the tools by asking what part of the proof needs clarity:

| Need | Typical tool |
| --- | --- |
| Normalize all safe occurrences toward a standard form | `simp` |
| Apply a theorem once at the selected matching occurrence | `rw` |
| Show a sequence of mathematical intermediate claims | `calc` |
| Rewrite inside a specific argument, side, hypothesis, or binder | `conv` |
| Prove a quantified function equality by pointwise reasoning | `funext` followed by ordinary tactics |

These tools can be combined. A `calc` line can contain a local `by` block that uses `conv`; a conversion step can invoke `simp`; and a rewrite can be followed by a calculation for the remaining inequalities. Keep each layer small so the proof remains easy to inspect.

### Calculations as proof boundaries

A calculation can also separate a fact that comes from a hypothesis from a fact that comes from algebra or order. For example, first substitute an equal value, then apply monotonicity. A named lemma can be placed at that boundary if the transition is reused elsewhere. This structure helps maintainers find the exact source of a failed proof after a library change: the failing step identifies the theorem or normalization that no longer matches.

When a `calc` block has many steps, inspect whether each intermediate expression is a useful normal form. If a line is present only because a tactic needed it during exploration, try to replace several low-level steps with a library theorem or one stronger intermediate lemma. Conversely, if one large step combines unrelated algebra and inequalities, split it so each relation has a clear justification.

## 8. Common failure modes

### The calculation has a broken endpoint

The right-hand expression on one line must match the left-hand expression on the next. If it does not, add the missing equality or rewrite the next statement to start from the actual endpoint.

### The relation changes without a transitivity path

Equality and inequalities can coexist in one calculation, but they still have to compose. Check that the relation provides the required transitivity and that each adjacent pair of expressions has compatible types.

### `conv` navigates to the wrong argument

Read the expression's function application and count arguments at the current focused term. Use `trace_state` or an editor goal view after a navigation step if the selected subterm is unclear. Keep each path short.

### A simple rewrite becomes a long conversion script

If `rw` or `simp` already targets the intended occurrence, use that. Conversion mode is valuable for exact scope, not as a replacement for every rewrite.

### A calculation repeats tactics instead of explaining the proof

Choose intermediate statements with mathematical meaning. If a step is not independently understandable, name the lemma or refine the endpoint rather than adding more syntax.

## 9. Exercises

1. Prove a transitive inequality with `calc` from two non-strict bounds followed by a strict bound.
2. Starting from `a = b` and `b + c = d`, prove `a + c = d` with a two-step calculation.
3. Prove an equality by rewriting one inner multiplication in a nested product with `conv`. Then compare the result with a proof using `ac_rfl` or `ring` when the algebraic structure allows it.
4. Rewrite `0 + x` only inside the body of a function using conversion mode. Compare this with a proof using `funext`.
5. Normalize one side of a hypothesis with `conv at h` while leaving another matching expression unchanged. State why a global rewrite is less suitable.
6. Take a long `rw` sequence from an existing development and refactor it into a `calc` block with one meaningful transition per line.

## Summary

Use `calc` to make a chain of equalities or inequalities read like a mathematical argument. Each line is a typed step, and consecutive endpoints must compose. Use `conv` when the location of a rewrite matters: it can focus one side, one argument, one hypothesis, or an expression under a binder. Prefer `simp` and `rw` for ordinary rewriting, reserving `conv` for targeted local changes. The best proof exposes the mathematical transitions without preserving every tactic used during exploration.

## Further reading

- [Theorem Proving in Lean 4: Calculational Proofs](https://lean-lang.org/theorem_proving_in_lean4/Quantifiers-and-Equality/)
- [Theorem Proving in Lean 4: The Conversion Tactic Mode](https://lean-lang.org/theorem_proving_in_lean4/The-Conversion-Tactic-Mode/)
- [Lean reference: Targeted Rewriting with `conv`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Targeted-Rewriting-with--conv/)

end Chapter10
