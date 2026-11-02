# Chapter 5 — Subtypes, Invariants, and Equivalences

> **Audience.** This chapter assumes you know functions, structures, and equality. It shows how to encode mathematical side conditions in types, how to build maps that preserve those conditions, and how to package mutually inverse maps as equivalences.

Mathematical definitions often restrict a familiar type: positive natural numbers, bounded indices, nonzero elements, or lists satisfying an invariant. A subtype represents such a restriction without discarding the original value. It pairs the value with evidence that the required property holds.

This representation changes proof obligations in a useful way. A function into a subtype must construct both an output and its property proof; equality of subtype values can usually be reduced to equality of their underlying values. The result is a clean boundary between ordinary data and the invariant that makes it mathematically valid.

## Learning objectives

By the end of the chapter, you should be able to:

- read a subtype as a value paired with a proof of a predicate;
- construct subtype values and use their underlying value and property;
- prove equality of subtype values with `Subtype.ext`;
- define maps that preserve invariants;
- package a bijective correspondence as an `Equiv` and use its inverse laws.

The Lean declarations in this chapter are grouped in `Chapter05`; the namespace remains open across the examples and closes after the inverse-law examples.

## 1. Encoding an invariant in a type

For a type `α` and predicate `p : α → Prop`, the subtype

```lean
{x : α // p x}
```

contains values `x : α` together with a proof of `p x`. A value is constructed with angle-bracket notation:

```lean
⟨x, proofOfP⟩
```

and inspected through its `.val` and `.property` fields. Here is the type of positive natural numbers:

```lean
namespace Chapter05

abbrev PositiveNat := {n : Nat // 0 < n}
```

The underlying value is still a natural number. The subtype records the additional fact that it is positive, so a function that receives a `PositiveNat` does not need to carry a separate hypothesis every time it uses the input.

```text
natural number n
      │
      │ provide a proof of 0 < n
      ▼
⟨n, proof⟩ : PositiveNat
```

The proof component lives in `Prop`, so it is not a second computational value. It is evidence attached to the number and checked by Lean.

## 2. Constructing values and preserving invariants

To define a function whose result is a subtype, construct the value and its proof together. For example, adding one to a positive natural number produces another positive natural number:

```lean
def succPositive (n : PositiveNat) : PositiveNat :=
  ⟨n.val + 1, Nat.succ_pos n.val⟩
```

The result's underlying value is `n.val + 1`; the second component proves it is positive. Once the output has this type, every caller can rely on its positivity without asking for a separate theorem.

More generally, a function `f : α → β` lifts to a function between subtypes when it preserves the chosen predicates:

```lean
def mapSubtype {α β : Type _} {p : α → Prop} {q : β → Prop}
    (f : α → β) (hf : ∀ x, p x → q (f x)) :
    {x // p x} → {y // q y} :=
  fun x => ⟨f x.val, hf x.val x.property⟩
```

This definition separates the computational map `f` from the preservation theorem `hf`. The value part applies `f` to the underlying element. The proof part applies `hf` to the element and the proof stored in the input subtype.

The same pattern appears in formalized mathematics whenever an operation preserves a property: map a nonzero element to another nonzero element, send a bounded index to a valid index, or transform a well-formed expression into another well-formed expression. Package the property into the type when later theorems should be allowed to assume it automatically.

The lifted map computes the expected underlying value, while the subtype carries the proof produced by `hf`:

```lean
example {α β : Type _} {p : α → Prop} {q : β → Prop}
    (f : α → β) (hf : ∀ x, p x → q (f x)) (x : {a // p a}) :
    (mapSubtype f hf x).val = f x.val := rfl
```

This distinction is valuable in a large development. Most theorems about the map should reason about the underlying function `f`; only the theorem that constructs the subtype result needs to supply the proof of `q`. The invariant is present whenever it is needed, but it does not clutter every equation about the value.

### Subtypes, structures, and proof assumptions

A subtype is particularly appropriate when the extra field is a proposition about the underlying value. If the extra fields are computational data—such as a chosen witness, an ordering, or a cached result—a structure is usually clearer. A structure can contain both data and proofs; a subtype specifically has a value plus a predicate proof.

This choice affects equality. For subtypes, `Subtype.ext` says that equality of underlying values suffices. For a general structure, the appropriate extensionality theorem may need to compare several data fields. Proof fields in either case are handled using proof irrelevance, but computational fields must be accounted for in the equality proof.

`Fin n` is a standard example of a subtype-like object: it represents a natural number together with evidence that the value is less than `n`. Using `Fin n` instead of a bare `Nat` makes the bound part of the type. Indexing a vector by `Fin n` then guarantees that a requested position is in range, so later access functions need no out-of-bounds case.

For example, the final position in a vector of length `n + 1` is a valid `Fin (n + 1)`:

```lean
def lastFin (n : Nat) : Fin (n + 1) :=
  ⟨n, by omega⟩

example (n : Nat) : (lastFin n).val = n := rfl
```

The constructor forces the proof that `n < n + 1` at the point where the index is created. Afterward, any function that accepts `Fin (n + 1)` may safely assume the bound. This is a common way to move routine side conditions out of theorem statements and into data construction.

Lean inserts coercions from many subtypes to their underlying values, so an expression involving a `PositiveNat` can often be used directly where a `Nat` is expected. In a proof or a library-facing theorem, writing `.val` explicitly can still help the reader see which representation is being used and can help Lean resolve an ambiguous expression.

## 3. Equality of subtype values

Two subtype values are equal when their underlying values are equal. Their proof fields need not be compared as mathematical data. The extensionality theorem expresses exactly this:

```lean
example (a b : PositiveNat) (h : a.val = b.val) : a = b := by
  apply Subtype.ext
  exact h
```

After `Subtype.ext`, the target is equality of the natural-number values. This connects directly to Chapter 4: equality of a richer object is reduced to equality of the observations that determine it.

Conversely, equality of subtype values immediately gives equality of the underlying values:

```lean
example (a b : PositiveNat) (h : a = b) : a.val = b.val := by
  exact congrArg Subtype.val h
```

`congrArg` applies the function `Subtype.val` to both sides of an equality. The equality is preserved because functions map equal inputs to equal outputs. This is often the right way to extract a useful consequence from equality of structured values.

The subtype's proof field is useful when constructing and reasoning about a value, but it usually does not belong in the final equality proof. Try `Subtype.ext` when a subtype equality goal seems to be asking you to prove an irrelevant comparison between two proofs.

## 4. From inverse maps to an equivalence

An **equivalence** is a pair of functions that are inverse to one another. Lean's `Equiv α β` packages a forward map, an inverse map, and proofs of both inverse laws.

As a running example, positive natural numbers are in bijection with all natural numbers: subtract one in the forward direction, then add one in the inverse direction. The positivity condition makes subtraction well behaved.

```lean
def positiveNatEquiv : PositiveNat ≃ Nat where
  toFun n := n.val - 1
  invFun n := ⟨n + 1, Nat.succ_pos n⟩
  left_inv n := by
    apply Subtype.ext
    exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr n.property)
  right_inv n := by
    exact Nat.add_sub_cancel_right n 1
```

The `left_inv` proof compares subtype values, so it first applies `Subtype.ext` and then proves the natural-number identity. The `right_inv` proof is an ordinary natural-number calculation. The `omega` tactic handles the subtraction and inequalities in both cases.

The correspondence can be pictured as two maps whose composites are identities:

```text
PositiveNat  ── positiveNatEquiv ──▶  Nat
     ▲                                  │
     └────────── inverse map ───────────┘

inverse ∘ forward = identity     forward ∘ inverse = identity
```

The inverse laws are not informal expectations. They are fields that Lean requires before it accepts the `Equiv` declaration. Once those laws are proved, the library can use them to simplify compositions, transport structure, and establish bijectivity.

The directions of the laws are worth writing down before defining an equivalence. If `f : A → B` and `g : B → A`, the obligations are

```text
g (f a) = a    for each a : A
f (g b) = b    for each b : B
```

These equations determine which function belongs in `toFun` and which in `invFun`. If one direction only works after restricting the domain, that restriction belongs in the source type—as it does for positive natural numbers—or the proposed correspondence is not an equivalence.

## 5. Use the equivalence interface

After defining an equivalence, prefer its named operations and laws instead of repeating the underlying arithmetic. The forward map is `positiveNatEquiv`; its inverse is `positiveNatEquiv.symm`. Generic theorems about equivalences can then be reused regardless of whether the example involves natural numbers, functions, or other structures.

An equivalence should be used when the mathematical objects correspond in both directions. If only a forward map exists, or if it is injective but not surjective, use the corresponding function property instead. Do not promise an inverse that the mathematics does not supply.

An equivalence also does not automatically preserve every additional operation. If the objects have order, addition, or a topology, prove those preservation properties separately or use a stronger bundled map when the library provides one. The `Equiv` interface guarantees a bijection; it does not silently claim that the map is an order isomorphism or an algebra homomorphism.

This distinction is important when moving between representations. The positive natural equivalence establishes a bijection of types. If a later theorem needs the order relation to be preserved, that fact needs its own statement. Keeping the basic correspondence separate from extra structure makes both interfaces clearer.

For instance, the inverse laws of an equivalence let Lean simplify a map followed by its inverse:

```lean
example (n : PositiveNat) :
    positiveNatEquiv.symm (positiveNatEquiv n) = n := by
  simp

example (n : Nat) :
    positiveNatEquiv (positiveNatEquiv.symm n) = n := by
  simp

end Chapter05
```

No arithmetic appears at the call site. The arithmetic was needed once, when the equivalence was constructed. The generic inverse laws are now part of its interface and work for any equivalence.

## 6. When to use a subtype

Subtypes are valuable when the property is stable and should be available at every use site. They are especially useful for:

- values satisfying a bound, such as `Fin n` or positive numbers;
- nonempty collections, nonzero elements, or normalized representatives;
- functions or data structures that must satisfy a well-formedness predicate;
- maps whose output validity is part of their contract.

They are less useful when the property is needed only once in a short proof. In that case, an ordinary value plus a local hypothesis may be easier to read. A subtype changes the type of every function and theorem that consumes the value, so use it when the invariant belongs to the mathematical object rather than merely to one argument in one proof.

Subtypes also make it easier to discover forgotten obligations. If a function cannot construct its return value without proving the property, Lean stops at the point where the invariant needs justification. This turns a side condition into part of the function's type-level contract.

There is also a cost: every caller now has a subtype value to construct or obtain, and every theorem may need to move between the subtype and its underlying type. A useful design question is whether later results repeatedly rely on the invariant. If they do, the subtype usually pays for itself. If the condition appears in only one isolated argument, a local hypothesis may keep the rest of the interface simpler.

## 7. Common proof patterns

### The constructor does not determine the property automatically

To construct `⟨x, h⟩`, the proof `h` must establish the exact predicate in the subtype. If Lean reports a type mismatch, inspect the expected property and the type of the proof before changing the underlying value.

### Equality is blocked by the proof component

Use `Subtype.ext` to reduce equality to the underlying values. If the underlying equality is already available, apply the theorem and finish with that fact.

### A map preserves the value but not the invariant

When defining `mapSubtype`, the missing piece is usually the preservation theorem `hf`. Prove that `p x` implies `q (f x)` as a separate mathematical lemma, then use it to construct the output subtype.

### A claimed equivalence has only one inverse law

Both composites must be identities. If one proof fails, check the proposed inverse and the underlying domain restriction. The positive-natural example works because the positivity field rules out the problematic value zero.

### A subtype seems to erase useful information

The underlying value is still available through `.val`, and its invariant is available through `.property`. A subtype hides neither one; it packages them so callers cannot accidentally use a value without its proof. If a theorem needs to remember additional computational information, add a structure field rather than trying to encode data as a proposition.

## 8. Exercises

1. Define the subtype of natural numbers bounded above by `n`. Construct an example value and prove that its underlying value is at most `n`.
2. Prove that two values in `{n : Nat // n ≠ 0}` are equal from equality of their underlying natural numbers, using `Subtype.ext`.
3. Define a function on a subtype and prove the property-preservation theorem needed to lift it with `mapSubtype`.
4. For `positiveNatEquiv`, prove explicitly that the forward map is injective and surjective by using the equivalence laws. Then compare that work with the generic facts available from `Equiv`.
5. Give a mathematical example where a bijection does not preserve the additional structure you care about. State what stronger kind of map would capture the required preservation law.

## Summary

Subtypes attach proofs of invariants to ordinary values. Their constructors force preservation obligations to be explicit, while `Subtype.ext` keeps proof fields out of ordinary equality reasoning. Use `Equiv` when two types are genuinely in bijective correspondence, and state additional structure-preservation laws separately.
