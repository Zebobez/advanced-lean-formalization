# Chapter 7 — Functional Induction and Well-Founded Recursion

> **Audience.** This chapter assumes you know structural recursion and ordinary induction. It studies definitions whose recursive calls are smaller in a mathematical measure rather than visibly nested inside the input, and the induction arguments that follow those calls.

Structural recursion works when a recursive call receives a direct subobject exposed by pattern matching. Many useful algorithms do not have that form. Euclid's algorithm recurses on a remainder; binary algorithms reduce an integer by division; recursive parsers may move through input according to a progress measure. Lean can accept such definitions when every recursive call decreases a well-founded measure.

The same measure guides the proof. If a function calls itself on an input that is smaller according to some relation, a correctness proof often needs an induction hypothesis for every smaller input. Choosing an induction principle that follows the call graph is the central technique in this chapter.

## Learning objectives

By the end of the chapter, you should be able to:

- recognize when a recursive call is not structurally smaller;
- select a measure that decreases at every recursive call;
- discharge simple termination goals with arithmetic facts;
- use strong induction to prove properties of a measure-recursive function;
- distinguish a terminating definition from an opaque `partial` function;
- diagnose proofs whose induction hypothesis does not cover the recursive calls.

The examples are in namespace `Chapter07`.

## 1. Why structural recursion is not enough

Suppose a computation reduces a natural number by repeatedly halving it. The recursive call no longer receives a constructor subterm of the original input. In the successor branch, `((n + 1) / 2)` is smaller than `n + 1`, but it is not visibly the tail of the `Nat.succ` constructor.

We can define a function that counts one step plus the number of steps remaining:

```lean
namespace Chapter07

def halfSteps : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + halfSteps ((n + 1) / 2)
termination_by n => n
decreasing_by
  simp_wf
  omega
```

The measure is the input itself. The termination obligation in the successor branch is that halving a positive natural number produces a smaller natural number. `simp_wf` simplifies the generated well-founded goal, and `omega` proves the remaining arithmetic inequality.

The declaration still defines a total function. Lean accepts it only after the recursive calls have been justified as decreasing. That proof is part of the definition's logical construction, even though ordinary uses of the function should focus on its equations and mathematical behavior.

The recursive equations are propositionally available:

```lean
@[simp] theorem halfSteps_zero : halfSteps 0 = 0 := by
  simp [halfSteps]

@[simp] theorem halfSteps_succ (n : Nat) :
    halfSteps (n + 1) = 1 + halfSteps ((n + 1) / 2) := by
  simp [halfSteps]
```

These equations form the interface for proofs. In contrast with the structurally recursive examples in Chapter 6, `rfl` is not the method to rely on for unfolding this function. Lean generates equation theorems for well-founded recursive definitions, and rewriting with those theorems exposes the intended branch.

## 2. Termination measures

A termination measure maps the current arguments to a type equipped with a well-founded relation. Each recursive call must produce a strictly smaller measure. For `halfSteps`, the relation is the ordinary `<` relation on natural numbers, and the measure is just `n`.

The general shape is:

```text
current input ── measure ──▶ current rank
recursive input ─ measure ──▶ smaller rank

prove: measure(recursive input) < measure(current input)
```

A good measure reflects progress made by the algorithm. Common choices include:

- a natural-number argument that shrinks after division or subtraction;
- the length of a list, string, or syntax tree being processed;
- a tuple of arguments with lexicographic order;
- a custom rank or complexity function.

The measure need not be an argument by itself. It can be an expression computed from several arguments. For instance, a recursive procedure that decreases its first argument until zero and then begins decreasing its second may use a lexicographic pair. The exact measure should be chosen from the recursive calls, not guessed from the function's intended result.

For a two-argument function such as the Euclidean algorithm, the second argument is a natural candidate: after the zero case, the recursive call replaces `(a, b)` with `(b, a % b)`, and the remainder is strictly less than `b` when `b` is positive. In Lean, an explicit `termination_by a b => b` tells the elaborator to use that argument as the rank. The arithmetic proof then establishes that the recursive remainder is smaller. This proof is not part of the algorithm's mathematical correctness; it only justifies that recursive evaluation terminates.

### Termination and correctness are different obligations

The termination proof establishes that the definition has a value for every input. It does not establish that the value is useful, unique in an informal specification, or mathematically correct for the intended algorithm. Those properties belong in separate theorems.

For example, `halfSteps` terminates because the input decreases. A theorem such as `halfSteps n ≤ n` is a correctness-style property. Its proof uses the recurrence and an induction argument, not the termination proof itself.

Keeping these obligations separate improves both the definition and the proof. The termination block should contain the facts needed to justify decrease. The theorem section should state the behavior and invariants that downstream results need.

## 3. Induction should follow recursive calls

The recursive call in `halfSteps` uses `(n + 1) / 2`, which is smaller than `n + 1`. An ordinary successor induction provides an induction hypothesis only for `n`, not for every smaller value. That hypothesis may not directly apply to the recursive argument.

Strong induction gives the needed hypothesis: when proving the result for `n`, assume it holds for every `m < n`. We can use it to establish a simple bound:

```lean
theorem halfSteps_le (n : Nat) : halfSteps n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [halfSteps]
      | succ k =>
          rw [halfSteps_succ]
          have hsmall : (k + 1) / 2 < k + 1 := by omega
          have hbound := ih ((k + 1) / 2) hsmall
          omega
```

The proof has a deliberate sequence:

1. Strong induction makes a hypothesis available for any smaller natural number.
2. The zero case simplifies by the base equation.
3. The successor case rewrites by the recursive equation.
4. Arithmetic proves the recursive argument is smaller.
5. The induction hypothesis bounds the recursive result.
6. `omega` combines the inequalities.

The proof follows the same decreasing argument as the definition, but it is a separate proof. This is the practical meaning of functional induction: structure the reasoning around the function's recursive calls. Sometimes ordinary structural induction already has the right shape; sometimes strong or well-founded induction is a better match.

### Generalize every changing argument

Suppose a recursive function carries both a measure and an accumulator. Induction on the measure alone can still leave an induction hypothesis that is too specific about the accumulator. Generalize any argument that changes across recursive calls, just as Chapter 1 generalized list accumulators and Chapter 6 generalized a suffix.

The proof-design question is not merely “Which input should I induct on?” Ask instead: “What will the recursive call change, and what statement must remain true for that changed input?” State the invariant so that it can be instantiated at exactly the recursive call site.

## 4. Well-founded relations beyond natural numbers

Natural-number measures are common, but the underlying idea uses a well-founded relation. A relation is well founded if there is no infinite descending chain. Lean uses a proof of well-foundedness to justify recursion and induction over that relation.

The relation may encode a structure more faithfully than a numeric rank. For example, syntax trees are naturally ordered by the proper-subterm relation; a compiler transformation may recurse on a smaller expression; and a pair of measures may be ordered lexicographically. A numeric encoding can work, but only if its proof obligations stay simpler than the relation it replaces.

Lean's well-founded recursion machinery can be understood conceptually as recursion over evidence that the current state is accessible: there is no infinite chain of smaller states below it. The programmer usually does not manipulate this accessibility proof directly. Instead, `termination_by` selects a measure and Lean generates the decrease obligations.

This perspective also explains why the matching induction theorem is available. If the function proceeds to arguments that are smaller under a well-founded relation, a proof can reason by well-founded induction over that same relation. Strong induction on `Nat` is a familiar special case: the current natural number is proved using all smaller natural numbers.

## 5. Equation lemmas for well-founded definitions

The equations of a structurally recursive function often compute by definitional equality. For well-founded recursion, the recursive equation is generally propositional: the function application is equal to the branch expression by a theorem. This affects both proof style and performance.

For `halfSteps`, name the equations and use them explicitly:

```lean
example (n : Nat) : halfSteps (n + 1) = 1 + halfSteps ((n + 1) / 2) := by
  rw [halfSteps_succ]
```

Here `rw` is intentionally explicit. It is clear which branch equation is used. If the equation is tagged `[simp]`, `simp` may perform the same rewrite automatically; use named rewrites when a proof should make the recursion step visible.

Avoid depending on the internal encoding of a well-founded definition. Unfolding it may reveal a fixed-point or accessibility construction that is far less readable than the original equation. Use the equation theorem generated by Lean, or provide a named theorem with a meaningful statement. The definition is the implementation; the equations are the interface.

### Why `rfl` can fail

If a goal is `halfSteps 4 = 1 + halfSteps 2`, the statement is mathematically a direct instance of the recursive equation. But well-founded recursion may elaborate through a fixpoint whose reduction does not appear as ordinary definitional equality. `rfl` asks Lean's kernel to compute both sides; it does not search for an equation theorem. A rewrite or simplification step supplies that theorem.

This is not a weakness in the definition. It is the expected difference between definitional computation and a propositionally proved equation. Treat the generated theorem as a normal tool in the API.

## 6. Termination tactics and readable obligations

Termination goals are often arithmetic, but the goal may contain elaborator-generated relation wrappers. `simp_wf` is designed to simplify well-founded termination goals into familiar inequalities. After that, a domain-specific tactic such as `omega` may finish the arithmetic.

If a termination proof fails, inspect the generated goal rather than adding tactics blindly. Ask:

- What are the old and new arguments at this recursive call?
- Which expression did `termination_by` choose as the measure?
- Is the desired strict inequality mathematically true in every branch?
- Which branch fact (positivity, nonzeroness, or a bound) is available locally?
- Did the function need a different measure or a better case split?

For example, `n / 2 < n` is false when `n = 0`. The base case must be handled before making the recursive call, or the decrease proof must have an assumption that rules out zero. A measure proof can expose a bug in the definition rather than a limitation of the tactic.

If `omega` does not solve a goal, first normalize the structural form with `simp_wf`, then provide any missing arithmetic lemma. Keep termination proof blocks short and local. A one-line decrease proof is easier to audit than a large tactic script that also unfolds the algorithm.

## 7. Partial functions are not a shortcut for proofs

Lean also has ways to define functions without proving termination, including `partial` definitions and partial fixpoints. These mechanisms serve specific programming needs. A `partial` function is opaque to ordinary logical unfolding, so its equations may be unavailable for mathematical reasoning. A partial fixpoint can expose equations in cases where its specification allows partial behavior, but it does not replace a termination proof for a total function whose every input should have a determined result.

For a theorem-oriented definition, prefer structural or well-founded recursion when the algorithm terminates on all inputs. The termination argument documents why the recursion is safe and preserves a useful equational theory. Reserve partial definitions for cases where partial computation is genuinely intended and their logical interface is understood.

Do not mark a definition `partial` merely because the termination proof is inconvenient. If the function is total, a suitable measure usually leads to a better API and supports proofs of correctness. If the algorithm can fail, model that failure in its result type, for example with `Option`, rather than making termination and definedness implicit.

## 8. A measure-driven proof checklist

When defining a recursive function that changes its input, work through this sequence:

1. Write the recursive equations in ordinary mathematics.
2. Identify which quantity decreases in each recursive branch.
3. Choose a well-founded relation for that quantity.
4. State the measure with `termination_by` if inference is unclear or an explicit measure makes the intent more readable.
5. Prove decrease using only the local facts from that branch.
6. State the function's equation lemmas or abstract specification.
7. Prove correctness by induction on the same measure, generalizing other changing state.

This separates algorithm design, termination, equation use, and correctness. Each proof obligation then has one job.

## 9. Common failure modes

### The selected measure does not decrease in every branch

Trace every recursive call separately. A measure that works for the common branch can fail in a boundary case. A tuple or lexicographic measure may be needed if one component decreases only after another reaches a boundary.

### Structural induction gives the wrong hypothesis

If the recursive call is on an arbitrary smaller value, ordinary induction may give an IH for the predecessor only. Use strong induction or well-founded induction matching the measure, and generalize any additional changing parameters.

### The termination proof is being used as a correctness theorem

Proving that the measure decreases says the recursion terminates. It does not prove an invariant or specification. State and prove those separately from the recurrence equations.

### `rfl` cannot unfold the recursive call

Use the generated equation theorem with `rw` or `simp`. Do not try to force reduction through internal fixed-point implementation details.

### The function was marked `partial` to avoid a proof

Revisit the intended behavior. If the function should terminate for all inputs, find the measure and prove it. If it may fail, express failure in the return type and choose an interface that supports the required reasoning.

## 10. Exercises

1. Define `halveAgain` using the recurrence `f 0 = 0` and `f (n + 1) = 1 + f ((n + 1) / 2)`. Give an explicit termination measure and prove the decrease obligation.
2. Prove a bound on `halfSteps` using `Nat.strong_induction_on`. Identify the exact inequality needed to apply the induction hypothesis.
3. Modify the recurrence to subtract one rather than halve. Explain why structural recursion can handle the resulting call more directly.
4. Define a two-argument recursive function whose first argument decreases until zero and whose second decreases afterward. Propose a lexicographic measure and list the branchwise decrease obligations.
5. For the Euclidean algorithm, explain why the second argument is a useful measure and which remainder theorem supplies the strict inequality.
6. Give an example where an accumulator changes in a recursive call. State an invariant that must be generalized before the induction begins.

## Summary

Well-founded recursion supports algorithms whose recursive calls are not direct substructures. A measure and well-founded relation justify each decrease; the generated equations provide a propositional interface to the function. Proofs should follow the recursive call graph, often using strong or well-founded induction and generalizing any state that changes. Keep termination separate from correctness, use equation lemmas instead of exposing internal recursion machinery, and reserve partial definitions for problems where partial behavior is genuinely intended.

## Further reading

- [Lean reference: Recursive Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)
- [Theorem Proving in Lean 4: Induction and Recursion](https://lean-lang.org/theorem_proving_in_lean4/Induction-and-Recursion/)

end Chapter07
