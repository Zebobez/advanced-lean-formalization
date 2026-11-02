# Chapter 6 — Recursive Definitions and Equation Lemmas

> **Audience.** This chapter assumes you can define functions by pattern matching and prove basic facts by induction. It focuses on the interface between a recursive definition and the theorems that use it: which equations Lean can reduce automatically, how to expose stable equations, and how to choose a representation that makes proofs manageable.

Recursive programs are often specified by equations. A function on lists has one equation for the empty list and another for a cons cell; a function on trees has one equation for each constructor. Lean checks that recursive calls are justified, then makes the defining equations available for computation and proof. The details of that interface matter: a recursive call may reduce by definitional equality, or an equation may need to be used as a theorem.

This chapter develops those distinctions using trees and lists. It also shows why accumulator-based implementations need generalized correctness statements, and how named equation lemmas turn an implementation into a useful mathematical interface.

## Learning objectives

By the end of the chapter, you should be able to:

- identify the constructor that justifies a structural recursive call;
- distinguish definitional reduction from a propositional equation theorem;
- state and use explicit equations for a recursive definition;
- prove correctness of an accumulator helper with a generalized invariant;
- decide when to expose implementation equations and when to prove an abstract specification.

The declarations are placed in `Chapter06`. The namespace remains open through the worked examples and exercises.

## 1. Recursion follows data structure

Consider a binary tree whose leaves contain values of type `α`:

```lean
namespace Chapter06

inductive Tree (α : Type _) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  deriving Repr
```

The two constructors describe two shapes. A leaf carries one value; a node carries two smaller trees. A function that traverses the tree should usually have one defining case for each shape:

```lean
@[expose] def mapTree (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .node left right => .node (mapTree f left) (mapTree f right)
```

The recursive calls receive `left` and `right`, which are direct subtrees of the input node. This is the structural decrease that makes the definition safe. The recursive equations mirror the constructors:

```lean
example (f : α → β) (a : α) :
    mapTree f (.leaf a) = .leaf (f a) := rfl

example (f : α → β) (l r : Tree α) :
    mapTree f (.node l r) = .node (mapTree f l) (mapTree f r) := rfl
```

The equations can often be used directly by `rfl` or `simp`. For example, the following computations reduce without a separate theorem:

```lean
example (f : α → β) (a : α) : mapTree f (.leaf a) = .leaf (f a) := rfl

example (f : α → β) (l r : Tree α) :
    mapTree f (.node l r) = .node (mapTree f l) (mapTree f r) := rfl
```

Lean's equation compiler translates pattern matching and recursion into definitions that its kernel can check. For structurally recursive definitions like this one, the constructor equations hold by definitional equality: after the input is known to be a constructor, unfolding the definition computes to the corresponding branch. This is why `rfl` suffices.

The connection between patterns and recursive calls is a design aid. When an equation is hard to prove, inspect its recursive calls. If each call recurses on a visibly smaller constructor argument, structural recursion may be appropriate. If the argument changes through arithmetic or another transformation, a separate measure may be needed; that case is the subject of Chapter 7.

## 2. A definition and its public equations

Definitional equality is convenient, but it is not the only way to reason about a recursive function. A theorem can state the equations explicitly and become the intended interface. In Lean's module system, an exported theorem that proves an equation by computation also needs the definition to be exposed for reduction. Mark that implementation with `@[expose]`; downstream users can still rely on the equation theorem instead of unfolding the body themselves. For `mapTree`, the interface is:

```lean
@[simp] theorem mapTree_leaf (f : α → β) (a : α) :
    mapTree f (.leaf a) = .leaf (f a) := rfl

@[simp] theorem mapTree_node (f : α → β) (l r : Tree α) :
    mapTree f (.node l r) = .node (mapTree f l) (mapTree f r) := rfl
```

The `@[simp]` attribute tells the simplifier that these equations are safe, directional rewrites. A goal involving `mapTree f (.node l r)` can now simplify to the constructor-shaped result without opening the implementation manually:

```lean
example (f : α → β) (l r : Tree α) :
    mapTree f (.node l r) = .node (mapTree f l) (mapTree f r) := by
  simp
```

For this tiny definition, the named theorems may appear redundant. Their value becomes clearer when the implementation changes. A proof that relies on a stable equation theorem can continue to work even if the body is later reorganized, provided the public equation remains true. Directly unfolding a definition couples a client proof to implementation details.

An equation lemma is not automatically a good simplification rule just because it is true. The rule should move expressions toward a predictable form. The tree equations do so: they expose the outer constructor and leave smaller recursive calls. By contrast, a rewrite rule that replaces an expression with a larger or more complicated expression can make simplification loop or obscure the goal. Chapter 2 develops this normal-form perspective in detail.

### Choosing a theorem statement

Suppose a library exposes `mapTree`. There are at least three levels of interface:

1. The raw definition, whose body users may unfold.
2. Equations that describe behavior on each constructor.
3. Abstract laws, such as preservation of composition or identity.

Each level serves a different purpose. The raw body is useful while implementing the function. Constructor equations are useful for reasoning by cases. Abstract laws are useful to users who do not care how the function traverses a tree. A robust API provides the least implementation detail needed by clients and proves the higher-level laws from those equations.

For example, the identity law can be stated without exposing a particular implementation strategy:

```lean
theorem mapTree_id (t : Tree α) : mapTree id t = t := by
  induction t with
  | leaf a => rfl
  | node l r ihLeft ihRight =>
      simp [mapTree, ihLeft, ihRight]
```

The induction mirrors the tree constructors, and the induction hypotheses cover the recursive subtrees. The equation lemmas let the simplifier expose the node case; the abstract theorem says what users actually need to know.

## 3. Recursive equations and induction hypotheses

An induction proof about a recursive function commonly follows the same shape as its definition. The tree identity proof has one branch per constructor. In the node branch, there are two induction hypotheses, one for each child. The recursive equation reduces the goal to precisely those smaller claims.

This alignment is not accidental. The inductive type supplies an induction principle, and structural recursion follows the same constructors. A useful proof-design sequence is:

```text
recursive definition
        │
        ▼
one case per constructor
        │
        ▼
induction on the same structure
        │
        ▼
recursive equations simplify the goal
```

When that sequence breaks, the mismatch is informative. Perhaps the theorem should be generalized, as in Chapter 1. Perhaps the implementation has an accumulator and the theorem needs an invariant relating the helper to the specification. Or perhaps the recursion is not structurally decreasing and requires a different induction principle.

Here is a second tree function that counts leaves:

```lean
@[expose] def leafCount : Tree α → Nat
  | .leaf _ => 1
  | .node left right => leafCount left + leafCount right

@[simp] theorem leafCount_leaf (a : α) : leafCount (.leaf a) = 1 := rfl

@[simp] theorem leafCount_node (l r : Tree α) :
    leafCount (.node l r) = leafCount l + leafCount r := rfl
```

The expected equation is now the recursive specification itself. A useful theorem is that mapping values leaves the count unchanged:

```lean
theorem leafCount_map (f : α → β) (t : Tree α) :
    leafCount (mapTree f t) = leafCount t := by
  induction t with
  | leaf a => rfl
  | node l r ihLeft ihRight =>
      simp [ihLeft, ihRight]
```

The proof needs no properties of `f`. The values change, but the tree shape does not. This is a good example of choosing a theorem that describes the mathematical interface rather than proving facts about every leaf value individually.

## 4. Accumulators change the right invariant

An implementation can be equivalent to a simple specification while using a different recursive shape. An accumulator is a common example. Define a specification that lists tree leaves from left to right:

```lean
def leaves : Tree α → List α
  | .leaf a => [a]
  | .node left right => leaves left ++ leaves right
```

The node case concatenates the results from both subtrees. An accumulator helper can avoid repeatedly rebuilding an intermediate result:

```lean
def leavesAcc : Tree α → List α → List α
  | .leaf a, acc => a :: acc
  | .node left right, acc => leavesAcc left (leavesAcc right acc)

def leavesFast (t : Tree α) : List α := leavesAcc t []
```

The helper's recursive shape differs from the specification. In the node branch, it processes the right tree with the current accumulator, then feeds that result through the left tree. The correct relationship is not merely `leavesAcc t [] = leaves t` stated from the start. To reason inductively, the accumulator must be arbitrary:

```lean
theorem leavesAcc_spec (t : Tree α) (acc : List α) :
    leavesAcc t acc = leaves t ++ acc := by
  induction t generalizing acc with
  | leaf a => rfl
  | node left right ihLeft ihRight =>
      simp [leavesAcc, leaves, ihLeft, ihRight, List.append_assoc]
```

The theorem states what the helper means for every accumulator. In the node case, the induction hypothesis for `left` must apply to the accumulator produced by processing `right`. If `acc` had been fixed to `[]`, that more general recursive call would not match the induction hypothesis. Generalizing the accumulator gives the induction hypothesis enough scope.

The top-level correctness theorem follows immediately:

```lean
theorem leavesFast_eq (t : Tree α) : leavesFast t = leaves t := by
  simp [leavesFast, leavesAcc_spec]
```

The proof has two layers. `leavesAcc_spec` relates the implementation helper to its invariant. `leavesFast_eq` instantiates that invariant with the empty list. This separation is useful even when performance is not the immediate concern: implementation and specification remain independently readable.

The same pattern appears in tail-recursive list functions, parser loops, worklist algorithms, and stateful traversals. First write down the meaning of the accumulator. Then generalize the theorem over it. A strong invariant is usually easier to prove than a narrowly phrased final result.

## 5. Equations that need theorem rewriting

Structural recursion is the simplest case because equations reduce definitionally. For well-founded recursion, the function's recursive equations are generally available as propositional theorems rather than as kernel computation. The practical interface remains equation-based, but `rfl` may no longer close the goal. Chapter 7 will use this distinction extensively.

This matters in theorem statements involving recursive functions. A type checker can decide definitional equality by unfolding transparent definitions and reducing computations. It does not automatically search for arbitrary propositional equalities. If two expressions are equal only because of a proved equation, use `rw`, `simp`, or a calculation to provide that theorem to the proof.

For example, if a recursive equation is named `step_eq`, a proof can make the chosen rewrite explicit:

```lean
variable (P Q : α → Prop) (step : α → α)
variable (step_eq : ∀ x, step x = x)
variable (proofOfQ : ∀ {x}, P x → Q x)

example (x : α) (h : P x) : Q (step x) := by
  rw [step_eq x]
  -- The goal now uses the right-hand side of the equation.
  exact proofOfQ h
```

The identifiers here are schematic; the important move is to separate equation application from the remaining mathematical argument. If a rewrite fails, inspect the exact term Lean has produced. The equation may be oriented the other way, its arguments may not match, or the relevant case hypothesis may be missing.

## 6. Case equations and inaccessible patterns

Pattern matching can produce equations that are less obvious than simple constructor recursion. A recursive definition may branch on a test, an arithmetic condition, or a dependent value. In those cases, writing a theorem with explicit assumptions can be clearer than relying on the reduction behavior of a particular pattern.

For instance, an equation for a function that branches on `n = 0` should expose which branch condition is in force. The proof can then simplify the conditional using that evidence. Rather than forcing a client to reproduce the implementation's pattern matching, provide a theorem whose hypotheses state the mathematical condition:

```lean
variable (stepNat : Nat → Nat) (baseCase : Nat)

theorem step_zero (n : Nat) (h : n = 0)
    (stepNat_zero : stepNat 0 = baseCase) : stepNat n = baseCase := by
  subst n
  exact stepNat_zero
```

When the input is a constructor pattern, Lean may know a variable is determined by another pattern component. Such variables can be inaccessible patterns: they document a value inferred from the surrounding match rather than add a new case to consider. This is another reason to inspect the elaborated goal instead of assuming every token in a pattern contributes an independent hypothesis.

In a public theorem, explicit assumptions and conclusions make the equation robust. They also give `simp` a well-defined direction. If a function's implementation changes but the case theorem remains valid, client proofs need not change.

## 7. When to unfold and when to rewrite

There are several reasonable ways to use a definition in a proof:

- `rfl` tests whether computation alone closes the goal.
- `simp [f]` unfolds `f` and simplifies the resulting expression.
- `rw [f_equation]` applies one named equation in a chosen location.
- `simp` uses equations already marked as simplification rules.

Choose the least aggressive method that exposes the needed structure. Unfolding a large definition can produce implementation details that bury the argument. Rewriting with one equation often leaves a much smaller goal. On the other hand, if the function is local and the whole point of the proof is to inspect its implementation, `simp [f]` can be concise.

The choice also communicates intent. If a proof uses `mapTree_id`, it depends on a mathematical law. If it unfolds `mapTree`, it depends on its recursive implementation. Both can be valid, but library code should prefer the abstract law when one exists.

When simplification does not use an equation, check whether the equation theorem is tagged `[simp]`, whether the term matches the theorem's left-hand side, and whether rewriting in that direction moves toward a simpler expression. Avoid registering both directions of the same equation as simplification rules.

## 8. Common failure modes

### The recursive call is not on a visible smaller argument

Pattern matching on a value does not by itself justify every recursive call. The recursive argument must be a constructor subterm, or Lean must be given a well-founded measure that decreases. A transformed argument such as `n / 2` is a different termination argument; see Chapter 7.

### The theorem unfolds too much

If `[simp]` or `simp [f]` expands an entire recursive definition, write a named equation and rewrite only the branch you need. Keep the public theorem stronger and simpler than the implementation when possible.

### An accumulator theorem is too specific

If the induction hypothesis only talks about the empty accumulator but the recursive call uses a nonempty one, generalize the accumulator before induction. State the invariant for arbitrary state, not only for the final initial state.

### `rfl` does not recognize an equation

Check whether the definition is structurally recursive and whether the input has reduced to a constructor. If the equation is propositional, use its theorem. `rfl` proves definitional equality; it does not invoke arbitrary lemmas.

### A proof depends on the implementation accidentally

If many client proofs unfold the same definition, consider exposing equation lemmas or a higher-level correctness theorem. A stable interface reduces the number of places that must change when the implementation is reorganized.

## 9. Exercises

1. Define a function `treeMap` on `Tree` under a fresh name, then prove that mapping the identity function returns the original tree.
2. Define a function that counts the values in a tree using a custom weight `w : α → Nat`. State the two constructor equations as named theorems.
3. Prove that `leafCount t = (leaves t).length` by induction on `t`. Identify which constructor equations expose each side of the goal.
4. Define a list accumulator that appends a fixed suffix to every element's output. State and prove an invariant quantified over the suffix.
5. For `leavesAcc_spec`, remove `generalizing acc` and inspect the induction hypothesis. Explain exactly why it no longer proves the node case.
6. Find a recursive definition in a Mathlib file. Identify its defining equations and one theorem that gives a more abstract property of its behavior.

## Summary

Recursive equations should follow the shape of the input data. Structural recursion makes constructor equations available by definitional reduction; named equation lemmas provide a readable and stable interface. Proofs of recursive functions often use the same induction structure as the definition. When an implementation carries an accumulator, prove a generalized invariant that explains the accumulator's meaning. Use implementation equations to expose cases, and prefer abstract laws for clients that do not need to know how the function is implemented.

## Further reading

- [Lean reference: Recursive Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)
- [Theorem Proving in Lean 4: Induction and Recursion](https://lean-lang.org/theorem_proving_in_lean4/Induction-and-Recursion/)

end Chapter06
