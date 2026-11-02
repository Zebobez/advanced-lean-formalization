# Chapter 8 — Indexed Families and Dependent Elimination

> **Audience.** This chapter assumes familiarity with inductive types, pattern matching, and basic dependent types. It focuses on the practical proof patterns that arise when a type carries an index such as a length, bound, or state.

An indexed family is a type whose elements record more than the kind of data they contain. A vector is indexed by its length, a finite index by its bound, and a typing judgment by the context and type it establishes. The index is part of the type, so a function that returns an indexed value must produce data with exactly the advertised index.

This extra precision often removes proof obligations from later code. It also makes pattern matching more dependent: when a constructor is selected, Lean learns equations about the indices. The key skill is to let those equations guide the cases rather than fighting them with casts and manual substitutions.

## Learning objectives

By the end of the chapter, you should be able to:

- read an inductive family and identify how each constructor changes its index;
- use dependent pattern matching to rule out impossible cases;
- define functions whose input and output indices are related;
- use equality of indices to transport a value when computation cannot align the types;
- distinguish a genuine index mismatch from a simplification problem;
- design statements that expose the index information needed by induction.

The examples use a small vector family in namespace `Chapter08`. Mathlib and Lean's core libraries provide vector-like types as well; the local family keeps the constructor and index behavior visible.

## 1. A vector indexed by its length

Here is a vector type with two constructors. The empty vector has length zero; adding an element to a vector of length `n` produces one of length `n + 1`:

```lean
namespace Chapter08

inductive Vec (α : Type _) : Nat → Type _ where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (Nat.succ n)
```

The type `Vec α n` describes vectors with elements in `α` and length `n`. Unlike an ordinary list paired with a separate length theorem, the length is part of the type. A vector of length 3 cannot be passed where a vector of length 4 is required.

The constructor types show how the index behaves:

```text
nil  : Vec α 0
cons : α → Vec α n → Vec α (n + 1)
```

Pattern matching on a vector reveals which constructor was used and therefore what its length must be. For example, there is no `nil` case when the input has type `Vec α (n + 1)`. Lean rules that case out from the index equation.

## 2. Elimination rules out impossible cases

A head function only accepts nonempty vectors. Its type does not need an option result because an empty input is unrepresentable:

```lean
def head {n : Nat} : Vec α (Nat.succ n) → α
  | .cons x _ => x
```

Only one constructor pattern is needed. The empty constructor would produce a vector of length zero, which cannot unify with the required length `n + 1`.

The tail is similarly defined without an empty case:

```lean
def tail {n : Nat} : Vec α (Nat.succ n) → Vec α n
  | .cons _ xs => xs
```

The result type tracks the index change caused by removing the first element. A list-based tail has to account for the empty list at runtime; this function's input type has already excluded that branch.

We can make the elimination visible in a theorem:

```lean
example {n : Nat} (v : Vec α (Nat.succ n)) :
    ∃ x xs, v = Vec.cons x xs := by
  cases v with
  | cons x xs => exact ⟨x, xs, rfl⟩
```

The `cases` tactic performs dependent elimination. It examines each constructor and checks whether its resulting index can equal the target index. The `nil` branch is contradictory, so no goal is created for it. The `cons` branch provides exactly the head and tail requested by the existential conclusion.

This behavior is stronger than ordinary case splitting on an unindexed datatype. The indices participate in deciding which branches are possible. When Lean reports that a case is impossible, inspect the constructor's index equation; it often explains why no proof of that branch is required.

## 3. Defining functions that change indices

Appending two vectors adds their lengths. We put the second vector's length first so the index follows the recursive structure of the first vector:

```lean
@[expose] def vappend {m n : Nat} : Vec α m → Vec α n → Vec α (n + m)
  | .nil, ys => ys
  | .cons x xs, ys => Vec.cons x (vappend xs ys)
```

Natural-number addition computes by recursion on its second argument. Here that argument is the first vector's length: `n + 0` reduces to `n`, and `n + Nat.succ m` reduces to `Nat.succ (n + m)`. The constructor branches therefore match by computation, without explicit casts. Since addition is commutative on `Nat`, `n + m` is the same total length as `m + n`; this order is chosen to fit the definition's recursion.

The two equations can be exposed as named lemmas:

```lean
@[simp] theorem vappend_nil {n : Nat} (ys : Vec α n) :
    vappend Vec.nil ys = ys := by
  simp [vappend]

@[simp] theorem vappend_cons {m n : Nat} (x : α)
    (xs : Vec α m) (ys : Vec α n) :
    vappend (Vec.cons x xs) ys = Vec.cons x (vappend xs ys) := by
  simp [vappend]
```

These equations are useful for calculation and proof. Their types also document the computational behavior without requiring a reader to inspect the definition.

A length-preserving map is another function whose type tracks an invariant. The input and output vectors have the same index:

```lean
def mapVec (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (mapVec f xs)

theorem mapVec_id (v : Vec α n) : mapVec id v = v := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [mapVec, ih]
```

The constructor case tells Lean that the input length is a successor and that the tail has the predecessor length. The induction hypothesis is therefore exactly about the recursive call. No separate theorem about the length is needed: the function's type already fixes it.

### Index arithmetic and definitional equality

Some index equalities reduce automatically because they use the same recursive definitions as the constructors. Other equalities are merely propositions. Lean does not treat commutativity of addition as definitional: `m + n` and `n + m` are mathematically equal, but they do not compute to the same expression in general.

If a goal differs only by a standard arithmetic normalization, try `simp`, `omega`, or an explicit theorem about addition before introducing a cast. Casts are appropriate when the values genuinely live at equal but differently expressed indices; they are noise when a simple rewrite can make the indices match.

## 4. Equality of indices and transport

An equality of indices permits a value to move between the corresponding types. Lean's equality eliminator provides this operation. For vectors, it can be written with transport notation:

```lean
def castVec {m n : Nat} (h : m = n) (xs : Vec α m) : Vec α n :=
  h ▸ xs
```

The expression `h ▸ xs` uses the equality `h` to replace the index `m` by `n` in the type of `xs`. If `h` is reflexivity, the transport reduces to the original value. In proofs, `cases h` can often eliminate the equality and turn the goal into the reflexive case.

Transport is sometimes unavoidable, especially when a theorem changes indices in a way that is mathematically but not definitionally equal. But it should usually be a boundary operation. If casts spread throughout a definition, look for a better index expression, an equality lemma that normalizes the indices, or a theorem statement whose type aligns with the constructors.

### Dependent pattern matching can refine local variables

When matching on a value in an indexed family, constructor selection can determine an index. For a vector of length `n + 1`, choosing the `cons` constructor tells Lean that the tail has length `n`. In more complex families, a constructor can also identify types, contexts, or states. These facts appear as refined local types in the branch.

This refinement is part of the branch context. Read the goal after `cases` or `match` before adding casts. Lean may already have substituted an index or eliminated an impossible case. A transport added too early can hide the simpler type Lean has already derived.

## 5. Finite indices are indexed data in everyday use

`Fin n` is an indexed family whose values are natural numbers strictly below `n`. It is used throughout Lean and Mathlib for positions in fixed-size data. A function receiving a `Fin n` does not need a separate proof that the position is in range; the bound is part of the value's type.

This is the same design principle as the vector example, even though users rarely define `Fin` themselves. Arrays and vectors can expose indexing functions whose domain is a `Fin` value. A lookup at a valid index is total, and the caller must construct or obtain a value that meets the bound before lookup is possible.

The connection between vectors and finite indices is conceptually useful: a vector of length `n` has exactly the positions represented by `Fin n`. Turning that observation into a formal equivalence requires a careful definition and proof, but the indices explain why both types eliminate out-of-range cases at the boundary.

## 6. Induction over indexed families

Induction on an indexed family carries the index information into each case. A vector induction principle has a base case at length zero and a cons case at length `n + 1`. The cons case includes an induction hypothesis for the tail, whose index is `n`.

For example, define a sum of natural-number entries:

```lean
def sumVec : Vec Nat n → Nat
  | .nil => 0
  | .cons x xs => x + sumVec xs
```

An induction theorem can establish that mapping zero-valued data preserves the sum, or that a relation holds for every entry. The important point is that the induction hypothesis is attached to the tail's exact index. If a proof also has a separate length variable or a state that changes in the recursive case, generalize it so the induction hypothesis matches the recursive call.

Suppose a theorem compares two vectors whose lengths are equal only by an explicit hypothesis. Before induction, decide whether to induct on one vector, both vectors, or the equality of indices. Dependent elimination may rewrite the second vector's index when the equality is eliminated. This can simplify the proof dramatically, but the order of `cases` matters: eliminate index equalities before choosing a constructor when those equalities determine which constructors are possible.

### A useful proof-state reading order

After dependent case analysis, inspect the local context in this order:

1. Which constructor was selected?
2. Which index equations follow from that constructor?
3. Which variables were refined or substituted?
4. Which recursive hypotheses now have a smaller index?
5. What is the exact target type in this branch?

This prevents many “type mismatch” detours. The mismatch often records a real relationship between the branch's indices, not an arbitrary elaboration problem.

## 7. Indexed families as invariants

An index is useful whenever a property can be represented in the type and should be available at every use site. Vectors encode length; `Fin n` encodes a natural number below `n`; typed syntax can encode the type of an expression; and a transition system may encode the current state in both input and output types.

Compared with a subtype, an indexed family can describe multiple constructors whose output indices differ. A subtype has one underlying value and one predicate. An indexed inductive type has constructors that create different shapes and indices. Use the representation that expresses the object's construction, not merely its validity condition.

The benefit is that impossible states become unrepresentable. A function receiving `Vec α (n + 1)` can define `head` without a failure branch. A function producing `Vec α (m + n)` promises the exact length relationship. A consumer does not need to reprove these facts from an ordinary list representation.

The cost is that definitions and theorems must keep indices aligned. A mathematically simple operation can produce a complicated type if its result index is written in a form that does not reduce in the required branch. Good index design is therefore part of API design.

## 8. Common failure modes

### Lean asks for a constructor case that seems impossible

Check whether the index equations actually contradict. If the index is abstract, Lean may not know a natural-number inequality or equality needed to eliminate the case. Provide the relevant index equality or use a dependent match that retains the equation.

### A result type differs by addition order

Associativity and commutativity are propositional, not definitional. Rewrite the index with the appropriate theorem or change the result type to follow the recursive constructor's natural expression. Avoid inserting `cast` before checking whether `simp` can normalize the index.

### Pattern matching loses an index relationship

Use a dependent match when the branch needs an equation linking the scrutinee to its pattern. An equation-style match can retain such evidence. Then eliminate or rewrite that evidence deliberately.

### Too many casts appear in a proof

Try eliminating the equality proof with `cases`, normalizing index arithmetic, or strengthening the induction statement. Repeated transports often signal that the theorem is phrased at incompatible indices.

### The induction hypothesis has the wrong index

Generalize the index-related variable or equality before induction. In dependent proofs, the order of generalization and induction is especially important: the induction hypothesis should be quantified over the values that change in recursive calls.

## 9. Exercises

1. Define a vector function that repeats a value exactly `n` times. State its result type and constructor equations.
2. Define a function that maps `f : α → β` over a vector without changing its length. Prove the result index is unchanged.
3. Prove that `head (Vec.cons x xs) = x` and `tail (Vec.cons x xs) = xs` by simplifying the definitions.
4. State a theorem that two vectors of different lengths cannot be equal when the lengths are known unequal. Identify which part of the type system enforces the contradiction.
5. Prove an associativity theorem for `vappend`. Pay attention to the index equality between `(m + n) + k` and `m + (n + k)`; use transport only after normalizing the equality you need.
6. Give an example from typed syntax where a constructor's index makes an otherwise possible case impossible.

## Summary

Indexed families put invariants such as length, bounds, and states into types. Dependent pattern matching uses those indices to refine cases and rule out impossible constructors. Definitions must align output indices with constructor arithmetic; ordinary equality lemmas may be needed when the indices are mathematically equal but not definitionally identical. Use transport for genuine type changes, eliminate equality evidence when possible, and generalize index-related state so induction hypotheses follow recursive calls.

## Further reading

- [Lean reference: Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)
- [Functional Programming in Lean: Indexed Families](https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/Indexed-Families/)

end Chapter08
