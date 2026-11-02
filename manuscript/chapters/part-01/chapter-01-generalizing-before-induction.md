# Chapter 1 — Generalize Before You Induct

> **Audience.** This chapter assumes that you can read Lean definitions, state theorems, and write basic tactic proofs. Its subject is proof design: how to choose an induction hypothesis that remains useful in the recursive case.

## Learning objectives

By the end of the chapter, you should be able to:

- predict which local variables Lean will keep fixed when you induct;
- detect when a recursive call changes an argument that the induction hypothesis has frozen;
- strengthen the induction motive with `generalizing` or `revert`;
- separate an induction-hypothesis mismatch from the algebraic rewriting needed after it is repaired.

Many difficult-looking induction failures have a simple cause: the proof is asking induction to prove a statement that is too specific. The recursive argument may change, but the induction hypothesis still remembers its old value. No amount of rewriting can make that hypothesis apply. The repair is often to strengthen the statement *before* induction.

We will study this technique through an accumulator-based list reverse. The example is small enough to inspect completely, but the same reasoning applies to recursive functions with environments, bounds, fuel, invariants, and other state.

## 1. A recursive function with moving state

Assume `import Mathlib` at the top of the file. Our helper takes a list of pending elements and an accumulator:

> **Definition 1.1 (reverse with an accumulator).** `reverseAcc xs acc` processes `xs` from left to right while accumulating the result in `acc`.

```lean
universe u

namespace Chapter01

def reverseAcc {α : Type u} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => reverseAcc xs (x :: acc)
```

The type is worth reading before the equations. It says that `reverseAcc` is not a function from lists to lists alone: it consumes a list and a second list that records state. The equations show how that state changes. In the empty case the computation is finished, so the result is exactly the accumulator. In the cons case the head moves from the pending list to the front of the accumulator.

The mathematical contract we want is

\\[
\operatorname{reverseAcc}(xs, a)
  = \operatorname{reverse}(xs) \mathbin{++} a.
\\]

This equation says that the helper's output is the ordinary reverse of its pending input, followed by whatever was already in the accumulator. It is stronger than a statement about a particular starting value such as `[]`. That extra generality is not decorative: it describes the actual interface of the helper and makes the induction hypothesis useful.

Each recursive call removes the head of the first list and pushes that element onto the accumulator. The expected relationship to the standard reverse is:

```lean
#check fun {α : Type u} (xs acc : List α) =>
  reverseAcc xs acc = xs.reverse ++ acc
```

The accumulator is part of the theorem because the helper is meant to work from *any* starting accumulator. That quantification will also be what makes the induction work.

> **Theorem 1.1 (accumulator reverse law).** For every pair of lists `xs` and `acc`, `reverseAcc xs acc = xs.reverse ++ acc`.

## 2. Diagnose the induction hypothesis

Consider beginning with an ordinary induction on `xs`. The proof state in the cons case looks like this:

```lean
induction xs with
| cons x xs ih =>
    -- ih is specialized to the original acc.
    -- The goal now calls reverseAcc xs (x :: acc).
```

In this case, the context contains

```text
ih   : reverseAcc xs acc = xs.reverse ++ acc
goal : reverseAcc xs (x :: acc) = (x :: xs).reverse ++ acc
```

The recursive call changed the accumulator from `acc` to `x :: acc`. The hypothesis only describes the old accumulator, so it cannot rewrite the recursive call. The issue is not that Lean failed to guess a clever tactic; the local theorem is too weak for the recursive step.

The mismatch can be seen without reading the entire goal:

```text
ordinary motive:    xs ↦ P xs acc
                         │ induction
                         ▼
induction gives:    P xs acc
recursive step needs P xs (x :: acc)      mismatch

generalized motive: xs ↦ ∀ acc, P xs acc
                         │ induction
                         ▼
induction gives:    ∀ acc, P xs acc
instantiate at:     x :: acc              usable hypothesis
```

Here `P` stands for the property being proved. Lean's printed context is the most reliable diagnostic, but this diagram captures the design question: should `acc` be a fixed parameter of the motive, or should it be quantified inside the motive?

This gives a reliable diagnostic: compare the arguments of the recursive call in the goal with the arguments appearing in the induction hypothesis. If an argument has changed, ask whether the hypothesis should have quantified over that argument.

## 3. Strengthen the motive

The useful induction statement is not a claim about one fixed `acc`. It is a claim that works for every accumulator:

```lean
#check fun {α : Type u} (xs : List α) =>
  ∀ acc : List α, reverseAcc xs acc = xs.reverse ++ acc
```

That is the motive we want induction to prove. In tactic mode, `generalizing acc` moves `acc` into the statement being proved by induction, then reintroduces it in each case. The induction hypothesis can therefore be instantiated at the changed accumulator.

```lean
@[simp] theorem reverseAcc_eq_reverse_append
    {α : Type u} (xs acc : List α) :
    reverseAcc xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      calc
        reverseAcc (x :: xs) acc = reverseAcc xs (x :: acc) := rfl
        _ = xs.reverse ++ (x :: acc) := ih (x :: acc)
        _ = xs.reverse ++ ([x] ++ acc) := rfl
        _ = (xs.reverse ++ [x]) ++ acc := by
          exact (List.append_assoc _ _ _).symm
        _ = (x :: xs).reverse ++ acc := by
          rw [List.reverse_cons]
```

The key line is `ih (x :: acc)`. That application is possible because the induction hypothesis is generalized over the accumulator. The remaining lines expose the list append associativity needed to match `reverse_cons`.

The `calc` block is intentional. It makes the proof's mathematical structure visible: unfold the recursive definition, apply the induction hypothesis to the new state, reassociate append, then use the reverse equation. A compact `simp` proof may also be possible, but the longer chain tells us exactly which fact repairs the mismatch.

### The same idea written with `revert`

`generalizing acc` is a compact way to change the induction motive. The underlying operation is to move `acc` back into the target before induction. The following is the same proof structure in a more explicit form:

```lean
theorem reverseAcc_eq_reverse_append_revert
    {α : Type u} (xs acc : List α) :
    reverseAcc xs acc = xs.reverse ++ acc := by
  revert acc
  induction xs with
  | nil =>
      intro acc
      rfl
  | cons x xs ih =>
      intro acc
      calc
        reverseAcc (x :: xs) acc = reverseAcc xs (x :: acc) := rfl
        _ = xs.reverse ++ (x :: acc) := ih (x :: acc)
        _ = xs.reverse ++ ([x] ++ acc) := rfl
        _ = (xs.reverse ++ [x]) ++ acc := by
          exact (List.append_assoc _ _ _).symm
        _ = (x :: xs).reverse ++ acc := by
          rw [List.reverse_cons]
```

This version is longer because each branch explicitly introduces the accumulator again. It is useful when you want to see the exact target before induction, or when several hypotheses and variables depend on one another. Once the dependency is clear, `generalizing acc` usually communicates the intention more economically.

## 4. Reading the motive, not just the tactic

The tactic call

```lean
induction xs generalizing acc
```

can be understood as asking Lean to prove the motive

```lean
#check fun {α : Type u} (xs : List α) =>
  fun acc : List α => reverseAcc xs acc = xs.reverse ++ acc
```

by induction on `xs`. This way of reading the proof is useful well beyond lists. When an induction hypothesis is too weak, write down the motive you actually need and identify the local variables that must move inside it.

You can express the same transformation by reverting `acc` before induction:

```lean
revert acc
induction xs
```

`generalizing acc` is usually more direct because it records the proof-design decision beside the induction. `revert` remains useful when the dependency is more involved or when you want to inspect the changed goal explicitly.

Do not generalize every variable automatically. A variable that stays unchanged through every recursive call can remain fixed. Generalize the variables whose values change in the recursive step, or whose generality is needed to make the induction hypothesis applicable.

## 5. A second worked example: appending through an accumulator

The same reasoning applies even when the updated state is not a constructor operation like `x :: acc`. Consider a helper that appends each pending element to the end of the accumulator:

```lean
@[expose] def pushBackAcc {α : Type u} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => pushBackAcc xs (acc ++ [x])
```

> **Definition 1.2 (append with an accumulator).** `pushBackAcc xs acc` appends each element of `xs` to the end of `acc`.

The expected law is that the helper leaves the accumulator first and appends the pending list after it:

> **Theorem 1.2 (append accumulator law).** For all lists `xs` and `acc`, `pushBackAcc xs acc = acc ++ xs`.

```lean
@[simp] theorem pushBackAcc_eq_append
    {α : Type u} (xs acc : List α) :
    pushBackAcc xs acc = acc ++ xs := by
  induction xs generalizing acc with
  | nil =>
      simp [pushBackAcc]
  | cons x xs ih =>
      calc
        pushBackAcc (x :: xs) acc = pushBackAcc xs (acc ++ [x]) := rfl
        _ = (acc ++ [x]) ++ xs := ih (acc ++ [x])
        _ = acc ++ (x :: xs) := by
          simpa using (List.append_assoc acc [x] xs)
end Chapter01
```

The critical step is still `ih (acc ++ [x])`. The recursive call changes the accumulator by appending `[x]`, so the induction hypothesis must be valid for that new value. The final equality is no longer about reverse; it is the algebra of list append. The proof architecture is unchanged: first make the hypothesis applicable, then finish the local calculation.

The lemma is marked `[simp]` because its right-hand side expresses the helper using the ordinary append operation. Later theorems can normalize away `pushBackAcc` without unfolding its recursive implementation. Chapter 2 develops the criteria behind this choice.

The state transition is:

```text
pending input             accumulator before
      x :: xs                    acc
          │ recursive step       │
          └──────────────┬────────┘
                         ▼
pending input             accumulator after
       xs                    acc ++ [x]
```

When designing the induction motive, follow the lower line of the recursive definition: every value that changes there is a candidate for generalization.

## 6. What exactly does generalization change?

It is useful to distinguish the statement of the theorem from the motive used internally by induction. The theorem we promised the reader is still

\\[
\operatorname{reverseAcc}(xs, a)
  = \operatorname{reverse}(xs) \mathbin{++} a.
\\]

Generalizing `acc` does not weaken that theorem or ask the reader to accept an extra assumption. It changes the temporary induction problem to a stronger one: prove the equation for every accumulator at once. The original theorem follows by applying that stronger result to the particular `acc` in the original context.

That is why strengthening is a productive proof move. A stronger induction hypothesis gives more information in each recursive case, while the base case must now establish the property for all possible accumulator values. In this example the base case is immediate, and the stronger motive exactly matches the recursive use.

More than one variable can be generalized:

```lean
induction xs generalizing acc bound
```

This should be a considered choice, not a ritual. Generalize a variable when the recursive call changes it or when the recursive case needs a result that is uniform in it. If several local declarations depend on one another, inspect their order and use `revert` when you want to control the dependency explicitly.

### The motive in logical form

Let `P xs acc` stand for the equation being proved. Ordinary induction with `acc` fixed asks for the motive

```text
Mfixed xs := P xs acc
```

so its induction hypothesis in the cons case is only `P xs acc`. Generalized induction instead asks for

```text
Mstrong xs := ∀ acc, P xs acc
```

and its step case has the shape

```text
(∀ acc, P xs acc) → ∀ acc, P (x :: xs) acc
```

Now instantiate the hypothesis with `x :: acc`, exactly the accumulator passed by the recursive equation. The tactic is not a special rule for accumulators; it asks induction to prove a stronger predicate on the structural argument.

This also explains why the type parameter `α` does not need to be generalized. It is unchanged by every recursive call. The recursive equation, rather than the variable's name or type, determines the useful motive.

### Generality is an invariant you maintain

After generalization, every branch must prove the law for an arbitrary accumulator. The base case is often easy because the recursive function reduces immediately, but it still checks that the proposed invariant is independent of the starting state. If the base case fails for a particular accumulator, the theorem may be false or the state may need to be represented differently.

In the cons case, apply the hypothesis to the exact value supplied by the definition. This is more disciplined than trying a succession of rewrites: the recursive call tells you which argument to use. For `reverseAcc` it is `x :: acc`; for `pushBackAcc` it is `acc ++ [x]`.

The following table is a prompt for inspecting recursive equations, not a mechanical recipe:

| Recursive definition passes | Candidate variable to generalize |
| --- | --- |
| `x :: acc` | the accumulator list `acc` |
| `acc ++ [x]` | the accumulator list `acc` |
| `fuel - 1` | the fuel parameter |
| a changed environment `env'` | the environment `env` |

Sometimes generalizing the changed argument is enough. In other proofs, the recursive case needs a stronger mathematical invariant in addition to the generalized variable. The induction hypothesis should state exactly what the next recursive call will need.

## 7. Common induction-design mistakes

### Inducting before inspecting the recursive equation

The datatype to induct on is often obvious, but the useful motive is not. Before writing `induction`, compare the recursive equation with the theorem statement. In the cons branch, `reverseAcc` passes `x :: acc`; `pushBackAcc` passes `acc ++ [x]`. Both equations tell us what the hypothesis must accept.

### Trying to rewrite with a hypothesis that does not match

If `rw [ih]` reports that the pattern was not found, do not immediately change the orientation or add a cast. Check whether the arguments in the target are literally the ones in `ih`. A transformed accumulator is a logical mismatch, not a syntactic inconvenience.

### Generalizing only after induction

Once Lean has constructed the induction cases, the original variable may no longer be available in the way you need. You can still restructure the proof with `revert`, but it is usually clearer to decide the motive before induction: `induction xs generalizing acc`.

### Generalizing everything

An unnecessarily broad motive can create larger hypotheses and harder base cases. It can also make the proof less readable because the induction hypothesis contains parameters unrelated to the recursive call. Start with the variables that change; add others only when the goal demonstrates that they are needed.

### Confusing `generalizing` with `generalize`

`generalizing acc` changes the induction motive by quantifying over an existing local variable. The `generalize` tactic instead replaces an expression in the target with a fresh variable and an equality. The names are related, but the proof operations are different. Use the tactic reference when you need expression replacement rather than a stronger induction hypothesis.

### Treating the first failed induction as wasted work

The failed attempt is a useful experiment: it reveals which variable the default motive holds fixed. The context produced by Lean is evidence about the theorem's shape. Record the changed argument, strengthen the motive, and reuse the same structural induction. This diagnostic is often more informative than immediately searching for a more powerful tactic.

## 8. A reusable workflow

When an induction step stalls, use this sequence:

1. **Expose the recursive call.** Reduce the recursive definition enough to see its arguments.
2. **Compare contexts.** Check the induction hypothesis against the recursive call, argument by argument.
3. **Find the changed state.** Look for an accumulator, bound, index, environment, or other parameter that has been updated.
4. **Strengthen the statement.** Generalize that variable before induction, then apply the hypothesis at the updated value.
5. **Finish with the local algebra.** Only after the hypothesis applies should you use associativity, rewriting, or simplification to align the expressions.

This workflow separates two different problems: a logical mismatch in the induction hypothesis and a rewriting problem in the goal. Solve them in that order.

## 9. Exercises

1. In the first induction attempt, write the exact type of `ih` and the exact recursive call that needs to be rewritten. Explain why `rw [ih]` cannot solve the mismatch.
2. Repeat the `reverseAcc` proof using `revert acc` instead of `generalizing acc`. Which version makes the motive more apparent to you?
3. In `pushBackAcc`, change the recursive update from `acc ++ [x]` to `x :: acc`. Predict the new closed-form theorem before trying induction. What operation on the original list appears in the result?
4. Define a function that recursively processes a list while also carrying a natural-number fuel parameter that decreases in each recursive call. State which variable should be generalized and why. You do not need to complete the proof.
5. Find a recursive theorem in your own work. Record the arguments of the recursive call and compare them with the induction hypothesis before writing any rewriting tactics.

### Check your understanding

- What exact mismatch makes the fixed-accumulator induction hypothesis unusable?
- What is the motive after `generalizing acc`?
- In a recursive theorem from your own work, which arguments change at the recursive call?

### Hint for Exercise 3

The changed update places each head at the front of the accumulator. Compare the result with the defining equations for `List.reverse`; the theorem will involve a reversed pending list, followed by the accumulator.

## Further reading

- The [Lean Language Reference: induction tactic](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) describes `induction e generalizing ...` as generalizing the listed local variables before induction and reintroducing them in each goal.
- *Theorem Proving in Lean 4*, [Induction and Recursion](https://lean-lang.org/theorem_proving_in_lean4/Induction-and-Recursion/), discusses induction principles generated for recursive functions.
