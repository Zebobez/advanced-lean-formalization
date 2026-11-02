# Chapter 4 — Prove Equality by Extensionality

> **Audience.** This chapter assumes you can work with equality and basic functions, sets, and structures. It focuses on a proof-design move that appears throughout advanced mathematics: replace equality of whole objects with equality of the observations that determine them.

Lean's equality is precise: a goal `x = y` asks for a proof that the two terms are equal. For functions, sets, and structured objects, the useful proof is often not a computation that makes the terms reduce to the same expression. Instead, one proves that every relevant input or field gives the same result. This principle is called **extensionality**.

Extensionality does not change what equality means. It gives a theorem that reduces equality of a particular kind of object to a family of smaller goals. In tactic mode, the `ext` tactic applies those theorems and exposes the observations that matter.

## Learning objectives

After this chapter, you should be able to:

- prove function equality from pointwise equality using `funext`;
- prove set equality by reducing it to membership equivalence;
- use `ext` to expose the fields or observations that determine an object;
- distinguish equality of propositions from logical equivalence;
- decide when extensionality is a better first move than unfolding or rewriting.

## 1. Functions are determined by their values

Suppose two functions `f` and `g` have the same output for every input. The theorem we want is

\\[
f = g.
\\]

The hypothesis, however, is a family of equalities indexed by the inputs:

\\[
\forall x,\; f(x) = g(x).
\\]

The function extensionality theorem, usually written `funext`, converts the pointwise statement into equality of functions:

```lean
example {α β : Type _} (f g : α → β)
    (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x
```

The tactic changes the goal from `f = g` to `f x = g x` for an arbitrary `x`. The hypothesis now has exactly the form needed.

```text
goal:      f = g
             │
             │ funext x
             ▼
new goal:  f x = g x
             │
             │ use h x
             ▼
          complete
```

This move is essential when two functions are not definitionally equal. Lean does not generally identify functions just because they happen to return the same answers; the proof must supply the pointwise argument.

### A worked example with compositions

Let `f : α → β` and `g : β → γ`. If two functions `u v : γ → δ` agree on every value in the range of `g`, then their compositions with `g` agree. Lean represents that reasoning by a pointwise proof:

```lean
example {α β γ : Type _} (g : α → β) (f₁ f₂ : β → γ)
    (h : ∀ x, f₁ x = f₂ x) : f₁ ∘ g = f₂ ∘ g := by
  funext x
  exact h (g x)
```

The important step is choosing the right input for `h`: the composition supplies `g x`. Extensionality exposes the argument; the surrounding definition tells us how to specialize the hypothesis.

Extensionality and congruence solve complementary problems. Extensionality turns equality of functions into pointwise goals. Conversely, once function equality is known, `congrArg` transports it through an application:

```lean
example {α β : Type _} (f g : α → β) (h : f = g) (x : α) :
    f x = g x := by
  exact congrArg (fun k : α → β => k x) h
```

This distinction helps when the equality is available at a different level than the desired conclusion. Use `funext` to build equality from pointwise facts; use `congrArg` to extract consequences from an equality you already have.

### Function equality when the output is a proposition

A relation is a function whose output is a proposition. To prove two relations equal from pointwise logical equivalence, first introduce the inputs with `funext`, then use propositional extensionality at the output:

```lean
example {α β : Type _} (R S : α → β → Prop)
    (h : ∀ a b, R a b ↔ S a b) : R = S := by
  funext a
  funext b
  exact propext (h a b)
```

There are two different extensionality steps here. The first two turn equality of functions into equality of their values. The final step turns equivalence of propositions into equality of propositions. Keeping those steps separate makes it clear which mathematical principle is doing the work.

For many goals, it is better not to form equality of proposition-valued functions at all. If the object is a set, use set extensionality and remain with membership equivalences. If a later theorem specifically asks for equality of relations, use the function and proposition extensionality chain above at that boundary.

### Simplify after exposing the input

Extensionality and simplification often work well together. First expose the arbitrary input, then let `simp` normalize the pointwise goal:

```lean
example : (fun n : Nat => n + 0) = fun n => n := by
  funext n
  simp
```

Before `funext`, the goal is equality between functions. After it, the target is the familiar arithmetic identity `n + 0 = n`. This ordering is a reliable pattern: use the structural theorem to reach the mathematical statement, then use the appropriate local simplification or algebraic argument.

## 2. Sets are determined by membership

A set `s : Set α` is represented by its membership predicate. Equality of sets is therefore proved by showing that every element belongs to one set exactly when it belongs to the other.

> **Theorem 4.1 (set extensionality).** If two sets have the same members, they are equal.

```lean
example {α : Type _} (s t : Set α)
    (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x
```

The `ext x` step applies the set extensionality rule and leaves an iff goal. An iff is the right conclusion here because membership is a proposition: an element may be shown to satisfy the predicate in both directions.

For example, suppose the sets are defined by different predicates:

```lean
def boundedBy (n : Nat) : Set Nat := {x | x < n}
def belowSucc (n : Nat) : Set Nat := {x | x < n + 1}
```

To prove these sets equal, the main work is a natural-number inequality equivalence. The outer structure of the proof is already determined:

```lean
example (n : Nat) : boundedBy n = {x | x < n} := by
  ext x
  rfl
```

This example is deliberately immediate, but it illustrates where the proof should begin. After `ext x`, the goal is a statement about membership, not equality of the set-building expressions. In a less trivial theorem, solve that membership goal with the relevant order lemma or arithmetic tactic.

The set representation also explains why `Set.ext` is often more useful than unfolding a set. Unfolding exposes a predicate; extensionality chooses the element and turns equality into a logical comparison of that predicate.

## 3. Structured objects are determined by their fields

Many mathematical objects are records: a carrier with operations, bounds, or auxiliary data. Equality of two records can be reduced to equality of the fields that determine them.

Consider a pair of natural-number bounds:

```lean
structure Bounds where
  lower : Nat
  upper : Nat
```

If the corresponding fields agree, the records are equal:

```lean
example (a b : Bounds)
    (h₁ : a.lower = b.lower) (h₂ : a.upper = b.upper) : a = b := by
  cases a with
  | mk al au =>
    cases b with
    | mk bl bu =>
      simp_all
```

The proof replaces each structure with its constructor, then uses the field equalities. For a product, an extensionality lemma exposes the two components:

```lean
example {α β : Type _} (p q : α × β)
    (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q := by
  ext <;> assumption
```

For custom structures, the library may already provide an extensionality theorem. If not, the proof can still be completed by destructuring both values, as in the previous example, or by stating a suitable extensionality theorem for later use. The tactic uses the extensionality lemmas available for the target type; its output tells you which observations the library considers sufficient to determine the object.

### Proof fields are not extra mathematical data

Subtypes and other dependent structures also contain proof fields. For a subtype

```lean
#check fun {α : Type*} (p : α → Prop) => {x : α // p x}
```

the value `x` is data and `p x` is evidence that the value satisfies a property. If two subtype values have equal underlying elements, their proof components do not create a new mathematical distinction. Proof irrelevance and the subtype extensionality theorem account for this:

```lean
example {α : Type _} {p : α → Prop}
    (x y : {a // p a}) (h : x.val = y.val) : x = y := by
  apply Subtype.ext
  exact h
```

Chapter 5 develops this representation in detail. For now, note the pattern: identify the data fields, prove them equal, and let extensionality handle the proof components.

## 4. Equality and equivalence are different goals

For ordinary values, the relevant property is equality `x = y`. For propositions, the natural comparison is often logical equivalence `P ↔ Q`. An extensionality theorem may turn a goal about functions into pointwise equality, or a goal about predicates into pointwise iff.

This distinction matters because Lean does not silently replace equality of propositions with logical equivalence. If the goal is `P = Q` but the proof gives `P ↔ Q`, use propositional extensionality explicitly:

```lean
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  exact propext h
```

For sets, the extensionality tactic chooses membership and produces an iff, so the proof stays in the natural logical form. For functions returning propositions, applying `funext` produces equality of propositions; `propext` can then convert the pointwise iff into that equality if needed.

Do not add `propext` just because a theorem mentions propositions. Use it only when the target really requires equality of propositions. Most set and predicate arguments can remain in the clearer form `P x ↔ Q x`.

## 5. Working deliberately with `ext`

The `ext` tactic is a proof-state transformation, not a search tactic that solves arbitrary equalities. It applies known extensionality principles until the goal reaches components such as function values, memberships, or record fields.

Use it in a controlled sequence:

1. Look at the type of the two objects being compared.
2. Predict what observations determine equality for that type.
3. Apply `ext`, optionally naming the element or index introduced.
4. Inspect the new goal and prove the resulting pointwise statement.

For a set, `ext x` records the element explicitly. For a function, `funext x` makes the pointwise argument explicit. For nested structures, `ext` may introduce several variables or leave multiple goals. That is useful information: the target contains several layers of observations.

If `ext` does not make progress, check whether the type has an extensionality lemma registered or whether the target should first be rewritten into a more recognizable form. Avoid repeatedly calling `ext` without inspecting the new goal; the correct endpoint is the simplest mathematical statement you can prove directly.

Extensionality lemmas form an API just like simplification lemmas. A library may register an `[ext]` theorem for a custom object so users can reduce equality to its public projections. Good extensionality theorems expose enough fields to characterize equality, but avoid unfolding unrelated implementation details. When the standard tactic stops at an unexpected point, inspect the generated goals and the available theorem rather than trying to force a different shape blindly.

The tactic also accepts explicit names for the elements or indices it introduces. Naming them can improve a long proof:

```lean
example {α β γ : Type*} (f g : α → β → γ)
    (h : ∀ x y, f x y = g x y) : f = g := by
  ext x y
  exact h x y
```

This is useful for relations, functions of several arguments, and nested collections. The names are ordinary local variables. They are not special placeholders; their order follows the successive extensionality steps, so inspect the resulting context before using them.

Not every object should be attacked with function extensionality. Lists, for example, are inductive sequences whose equality is usually proved by matching their constructors or applying a structural theorem. Extensionality is most effective when the object's mathematical identity is already characterized by its observations: function values, set membership, or record fields. If that characterization is not the right one, ordinary induction or a specialized equality theorem may be more direct.

Before applying `ext`, check whether the equality is already definitional or whether a library theorem gives a stronger direct result. Extensionality can turn one compact goal into many pointwise goals. That is the right trade when the pointwise statement is easier; it is unnecessary work when the two sides already reduce to the same term or when a named theorem closes the equality immediately.

## 6. Common mistakes

### Rewriting before exposing the observations

If the goal is `f = g` and the available fact is pointwise, rewriting may have nothing to match at the function level. Apply `funext` first, then use the hypothesis on an arbitrary input.

### Proving too much by unfolding

Unfolding a set or structure can expose implementation details without identifying the right logical obligation. Extensionality usually gives a smaller and more meaningful target.

### Using `rfl` for pointwise facts

`rfl` closes goals where both sides reduce to the same expression. It cannot prove a general function equality from a non-definitional hypothesis. Use `funext` to turn the target into the fact you actually know.

### Confusing equality of predicates with iff

For propositions, equality and logical equivalence are distinct Lean goals. If the mathematics provides an iff, keep it as an iff unless the surrounding theorem specifically requires equality; use `propext` at that boundary.

## 7. Exercises

1. Prove that two functions `f g : α → β` are equal from `∀ x, f x = g x`, using `funext` and no other automation.
2. Prove equality of two sets from pointwise equivalence of their membership predicates. Then repeat the proof for sets defined by inequalities over `Nat`.
3. Add a third field to `Bounds` and extend the equality proof. Which part of the proof becomes repetitive? How would an extensionality lemma improve it?
4. For predicates `P Q : α → Prop`, prove `P = Q` from `∀ x, P x ↔ Q x`. Identify the exact point where propositional extensionality is needed.
5. Give an example where `rfl` proves equality of two functions because their definitions reduce identically, and compare it with the pointwise proof of the same equality using `funext`.

## Summary

Extensionality turns equality of large objects into equality of their observable components. Use `funext` for functions, set extensionality for membership, and structure-specific extensionality for records. Keep equality and logical equivalence distinct, and inspect each generated goal before choosing the next proof step.
