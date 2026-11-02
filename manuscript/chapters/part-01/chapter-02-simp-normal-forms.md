# Chapter 2 — Make Simplification Predictable

> **Audience.** This chapter assumes you have used `simp` and `rw`. It focuses on how to make simplification behave like a stable interface in a growing development.

## Learning objectives

After this chapter, you should be able to:

- explain the normal form a simplification theorem is intended to establish;
- decide whether a theorem belongs in the global simp set or only in one proof;
- choose among `simp`, `simp only`, `simpa`, and simplification at a hypothesis;
- keep algebraic normalization separate from routine rewriting;
- diagnose whether a failed `simp` call is missing a rule or exposing a deeper proof obligation.

In a short proof, `simp` can feel like a convenient way to finish. In a large formalization, it is more useful to think of it as a rewriting engine with an API: the lemmas in its database determine which expressions count as simple, and the direction of each lemma determines the normal forms proofs will see.

The practical goal is not to make `simp` solve every goal. It is to give it a small, coherent set of rules so that routine normalization is predictable and the remaining mathematical argument stays visible.

## 1. Simplification is directed rewriting

An equality can be read in either direction as mathematics. The simplifier needs a direction. It normally applies a rule from the left-hand side to the right-hand side, repeatedly simplifying subexpressions along the way.

For example, a rule of the form `f (g x) = x` removes two layers of structure. It points toward a simpler expression, which we can picture as \\(f (g x) \mapsto x\\):

```text
f (g x)  ↦  x
```

A good simplification rule therefore has a recognizable left-hand side and a right-hand side that is closer to the representation you want to keep. This preferred representation is the rule set's **normal form**.

For this chapter, we will use the following informal model. A simplifier call starts with an expression, applies available rules in their chosen directions, simplifies the resulting subexpressions, and checks whether the result is definitionally or propositionally sufficient for the goal. It can use assumptions to discharge conditional steps. It does not search for every mathematically equivalent expression, and it does not invent a theorem that is absent from its rule set.

The direction matters because equality is symmetric while a rewrite system needs a preferred side. For instance, the rule

\\[
f(g(x)) = x
\\]

shrinks a term. The reverse rule expands `x` into `f (g x)`, making expressions larger and obscuring their simpler representation. The picture is a pipeline toward one chosen form:

```text
an expression with an implementation detail
                  │
                  │ oriented simp rule
                  ▼
an expression in the public vocabulary
```

This is why theorem attributes are part of proof architecture. A declaration tagged `[simp]` affects later proofs throughout the scope where that declaration is imported.

Chapter 1 proved the accumulator law and registered it as a simplification rule. Inspect the imported declaration:

```lean
#print Chapter01.reverseAcc_eq_reverse_append
```

Because this law removes the helper call and exposes the standard list operations, a later proof can use the normal form directly:

```lean
example {α : Type _} (xs acc : List α) :
    Chapter01.reverseAcc xs acc = xs.reverse ++ acc := by
  simpa only [Chapter01.reverseAcc_eq_reverse_append]
```

The point is not that one line is better than the proof in Chapter 1. The attribute says that other theorems may rely on the same public simplification rule without knowing how `reverseAcc` is implemented.

The output of this particular rule is easy to inspect:

```text
Chapter01.reverseAcc xs acc
              │
              │ reverseAcc_eq_reverse_append
              ▼
xs.reverse ++ acc
```

The rule removes the helper but preserves the mathematical content. It is a useful example of an abstraction boundary: the proof of the implementation law belongs with the definition, while clients use the standard list operation.

## 2. Publish only stable reductions

Here is a small example where a custom operation has a useful, predictable reduction law.

> **Definition 2.1 (pair swap).** The operation reverses the order of the two components of a pair.

```lean
namespace Chapter02

def swapPair {α β : Type _} (p : α × β) : β × α :=
  (p.2, p.1)

-- Theorem 2.1: swapping twice is the identity.
@[simp] theorem swapPair_involutive {α β : Type _} (p : α × β) :
    swapPair (swapPair p) = p := by
  cases p
  rfl

example {α β : Type _} (p : α × β) :
    swapPair (swapPair (swapPair (swapPair p))) = p := by
  simp

end Chapter02
```

The marked theorem removes a pair of swaps. It does not expand every `swapPair` into projections; it exposes exactly the useful law and leaves the representation abstract. This is a good shape for a global `[simp]` theorem: it is valid for every pair and consistently reduces a composite expression.

The simplifier is allowed to use that law inside a larger expression as well. If a pair is stored inside a record, tuple, or function argument, congruence rules let simplification descend into the expression and simplify the relevant subterm. This is one reason a small API of well-oriented theorems is more reusable than a long proof that only works after manually exposing the outermost definition.

By contrast, a theorem should not receive `[simp]` merely because it is true or easy to prove. Ask what a reader expects the expression to look like after simplification. If two rules pull the same expression in competing directions, or if a rule expands an abstract operation into implementation details, keep it local to the proof that needs it.

## 3. Choose the smallest simplifier scope

Lean offers several ways to choose rewrite rules. Use the narrowest scope that communicates the intent of the proof.

### Use `simp` for the established normal form

When the standard simp set already contains the needed rules, a plain `simp` states that the goal is routine normalization. For example, the standard list API includes the reverse-of-reverse law:

```lean
example {α : Type _} (xs : List α) : xs.reverse.reverse = xs := by
  simp
```

### Use `simp [definition]` to unfold a local definition

When a proof is about a definition's implementation, name that definition explicitly:

```lean
def addZeros (n : Nat) : Nat := (n + 0) + 0

theorem addZeros_eq (n : Nat) : addZeros n = n := by
  simp [addZeros]
```

The proof has a short normalization path:

```text
addZeros n
   │ unfold addZeros locally
   ▼
(n + 0) + 0
   │ Nat.add_zero
   ▼
n
```

This keeps the unfolding request local to this proof. It does not make every use of `addZeros` unfold automatically in unrelated theorems.

### Use `simp only` when the rule set matters

For a small normalization step, `simp only` records the precise rule set:

```lean
example (n : Nat) : (n + 0) + 0 = n := by
  simp only [Nat.add_zero]
```

This is useful when a proof should not depend on unrelated global simp lemmas. It is also a good way to diagnose a proof: add just the rule you expect, and see whether the remaining expression really has the shape you think it does.

### Use `simpa using` to align a known result

If a hypothesis proves the same fact in a slightly different, simplifiable form, let `simpa` normalize both sides of the comparison:

```lean
example (n m : Nat) (h : n = m) : n + 0 = m := by
  simpa using h
```

Read this as: simplify the type of `h` and the goal, then check that they agree. If the gap requires a substantive theorem rather than normalization, use that theorem explicitly instead of asking `simpa` to conceal the reasoning.

The same idea applies when the expression to normalize is in a hypothesis:

```lean
example (n m : Nat) (h : n + 0 = m) : n = m := by
  simpa using h
```

When you need to retain and inspect the simplified hypothesis, target it directly:

```lean
example (n m : Nat) (h : n + 0 = m) : n = m := by
  simp only [Nat.add_zero] at h
  exact h
```

The first proof treats simplification as a bridge between two equivalent surface forms. The second records exactly how the local context was normalized. For a longer proof, changing a hypothesis can make later steps clearer; for a short proof, `simpa using h` avoids introducing a context mutation.

### Use hypotheses to simplify conditional definitions

Simplification can use a proposition already known in the context to resolve a conditional branch. Here is a small function whose behavior depends on a proposition:

```lean
namespace Chapter02

def chooseFrom {α : Type _} (p : Prop) [Decidable p] (yes no : α) : α :=
  if p then yes else no

@[simp] theorem chooseFrom_of_true {α : Type _} (p : Prop) [Decidable p]
    (hp : p) (yes no : α) : chooseFrom p yes no = yes := by
  simp [chooseFrom, hp]

@[simp] theorem chooseFrom_of_false {α : Type _} (p : Prop) [Decidable p]
    (hp : ¬ p) (yes no : α) : chooseFrom p yes no = no := by
  simp [chooseFrom, hp]

example {α : Type _} (p : Prop) [Decidable p] (hp : p) (yes no : α) :
    chooseFrom p yes no = yes := by
  exact chooseFrom_of_true p hp yes no

end Chapter02
```

The hypotheses `hp` determine which branch is selected. The pattern generalizes to definitions using `if`, `dite`, and pattern matches: expose the definition locally, then let simplification use the relevant constructor or proposition. Avoid marking the entire implementation `[simp]` when two small behavioral laws give clients the stable interface they need.

Notice the boundary between the two proofs. The theorem statements `chooseFrom_of_true` and `chooseFrom_of_false` are the public interface. Their proofs unfold `chooseFrom` and use the proposition to select a branch. A later caller uses the `[simp]` theorem and need not repeat either implementation detail. This is the same separation used for `reverseAcc`: unfold while proving the law, then simplify by the law afterward.

## 4. Keep algebraic reasoning in its proper tool

The simplifier is strongest when the target has an obvious canonical direction. It is not a replacement for every normalization procedure. For example, commutative algebraic rearrangement is usually clearer with a domain-specific tactic:

```lean
example (a b c : ℤ) : a + b + c = c + b + a := by
  ring
```

The proof says that polynomial normalization is the intended argument. Adding a collection of commutativity and associativity lemmas to a simp set would make ordinary simplification less focused and would obscure which algebraic fact is doing the work.

The same separation helps when a proof has two phases. First normalize with `simp`; then prove the remaining algebraic identity with a tool such as `ring`, `omega`, or a direct lemma. Small steps make failures easier to interpret.

For example, if `simp` turns a goal into an equality of polynomials, the new goal is useful information: it shows that structural simplification has finished and algebra is now the real task. Calling `ring` at that boundary states the intended method. If `simp` does not reach that boundary, inspect the expression and add only the missing structural fact.

## 5. Read simplification failures as interface feedback

When `simp` does not close a goal, inspect the remainder before adding more rules.

- If the expression contains a definition you control, try `simp [thatDefinition]` locally.
- If a theorem is missing, state the mathematical law and decide whether it is a stable global simplification rule or a local rewrite.
- If a hypothesis has the right content but a different surface form, try `simpa using h`.
- If simplification removes too much or uses an unexpected rule, replace `simp` with `simp only [...]` to narrow the rule set.
- If the remaining goal is algebraic, use the tactic or theorem designed for that algebraic structure.

Avoid making a broad global simp change just to fix one proof. A new global rule changes the behavior of every later `simp` call in the project. Treat that as an API change and ask whether all of those callers should observe the new normal form.

One common source of confusion is that mathematical equivalence is broader than simplifier reach. Two expressions can denote the same value and still remain syntactically different after `simp` if the needed theorem is not in the active rule set. This is not a defect: it keeps simplification controlled. Add the missing fact explicitly, or choose a dedicated decision procedure for the remaining theory.

Another common source is simplifying the wrong object. If the target is already right but a hypothesis is not, use `simp ... at h`; if the hypothesis and target both need normalization, `simpa using h` often states the intent best. The `at *` location can be useful during exploration, but it may rewrite more of the context than a reader expects. Prefer naming the hypotheses when the proof's reasoning depends on the exact context.

The reverse caution also matters: `simp only` is not automatically more robust than `simp`. It gives a proof precise control of the active rules, which is valuable at a normalization boundary. But a long list of internal lemmas can couple the proof to implementation details. Prefer a small public lemma when a common normalization deserves a name, and use `simp only` when the exact local rewrite is itself part of the explanation.

## 6. A normal-form review for new lemmas

Before adding `@[simp]` to a theorem, check these points:

1. **Direction:** Does rewriting left to right move toward a clear canonical form?
2. **Termination:** Will repeated applications make progress rather than grow the expression or cycle through alternatives?
3. **Abstraction:** Does the right-hand side expose the intended public interface, or leak implementation details?
4. **Generality:** Is the law useful and unconditional enough to affect proofs throughout the development?
5. **Locality:** Would `simp [lemma]` or `simp only [lemma]` express the one proof's needs more accurately?

Also check the cost of the rule set. A theorem with complicated side conditions, heavy recursive structure, or an unexpected right-hand side may be mathematically valid but still be a poor default simplification rule. Keep such a theorem available by name and invoke it where its use is intentional.

For instance, the `reverseAcc` law is a sensible public rule when the development wants to reason about the standard `List.reverse` operation rather than the helper's internal recursion. If performance proofs need to preserve the accumulator implementation, they can use the underlying definition or a more targeted rewrite instead.

## 7. Exercises

1. In Chapter 1, `pushBackAcc xs acc` was shown to equal `acc ++ xs`. Would you mark that theorem `[simp]` in a library? State the normal form it establishes and give one case where automatic rewriting would help and one where it might be surprising.
2. Write a theorem for your own small helper function that removes one layer of that function from an expression. Decide whether it deserves `[simp]`, then demonstrate the decision with both `simp` and `simp only`.
3. Given the goal `a + b + c = c + b + a` over integers, explain why `ring` is a better fit than expanding the global simp set with rearrangement rules.
4. Take one of your existing proofs that ends in `simp`. Replace it with `simp only` and list the rules it actually needs. What does that list reveal about the proof's interface?
5. For `chooseFrom`, add an example where `hp : p` is in the context and simplify `chooseFrom p yes no`. Then remove `hp`. Which part of the expression remains unresolved, and why?
6. Consider the equation `a + b = b + a`. Explain why its truth does not by itself determine which side should be a global simplification normal form. Give one context where a local rewrite is still appropriate.

## Summary

Treat `[simp]` lemmas as part of the library interface. Orient them toward a stable normal form, keep implementation unfolding local, and use `simp only` when the exact rule set matters. Then the simplifier can take care of routine normalization without hiding the mathematics that deserves its own proof.
