# Chapter 13 — Homomorphisms, Embeddings, and Isomorphisms

> **Audience.** This chapter assumes familiarity with algebraic structures, functions, and equivalences. It explains how bundled maps record both an underlying function and the laws that make it preserve structure.

A raw function says how to send elements from one type to another. It does not say whether the function preserves multiplication, addition, order, or any other structure. Repeating those preservation hypotheses in every theorem makes a development verbose and easy to misuse. A bundled map packages the function with the laws that define its mathematical role.

Mathlib provides families of bundled maps: monoid homomorphisms, ring homomorphisms, linear maps, order homomorphisms, embeddings, and isomorphisms. Choosing the right bundle gives a proof access to generic theorems while keeping the map's guarantees in its type.

## Learning objectives

By the end of the chapter, you should be able to:

- distinguish a structure-preserving map from an arbitrary function;
- read common bundled map notations such as `M →* N` and `R →+* S`;
- use the map laws supplied by a homomorphism;
- prove equality of bundled maps extensionally;
- separate preservation of structure from injectivity or surjectivity;
- choose between a homomorphism, embedding, equivalence, and structured isomorphism.

## 1. A homomorphism carries a contract

A monoid homomorphism `f : M →* N` contains a function from `M` to `N` and proofs that it preserves the identity and multiplication. The function can be applied as if it were an ordinary function, but the structure laws are also available:

```lean
namespace Chapter13

example {M N : Type _} [Monoid M] [Monoid N]
    (f : M →* N) (a b : M) : f (a * b) = f a * f b := by
  exact map_mul f a b
```

The map laws are not facts that callers need to restate. They are part of the homomorphism interface. The corresponding generic theorem for powers follows from preservation of multiplication and identity:

```lean
example {M N : Type _} [Monoid M] [Monoid N]
    (f : M →* N) (a : M) (n : Nat) : f (a ^ n) = f a ^ n := by
  exact map_pow f a n
```

The exact notation depends on the structure being preserved. Common examples include:

- `M →* N` for a monoid homomorphism;
- `R →+* S` for a ring homomorphism;
- `M →ₗ[R] N` for a linear map over `R`;
- `α →o β` for a monotone map between ordered types;
- `M ≃* N` for a multiplicative equivalence.

The notation is part of the mathematical API. Read it before unfolding the underlying structure: it tells you what the map is expected to preserve.

The source and target structures matter independently. A monoid homomorphism needs a multiplication and identity in both types; a ring homomorphism also preserves the additive and multiplicative operations and their distinguished elements. A linear map depends on a scalar type and module structures. The bundled type makes these assumptions visible in the signature, so theorem application checks that the source and target really provide the required operations.

This lets one theorem cover many concrete maps. If a result only needs multiplication preservation, state it for a `MonoidHom`, not for a specific map or an unnecessarily strong ring equivalence. The theorem can then be reused for products, quotients, endomorphisms, and maps introduced by downstream files.

## 2. Constructing a bundled map

To define a homomorphism, provide its underlying function and prove each required preservation law. Projection from a product monoid is a simple example:

```lean
def firstProjectionHom {M N : Type _} [Monoid M] [Monoid N] : M × N →* M where
  toFun := Prod.fst
  map_one' := rfl
  map_mul' x y := rfl
```

The proof fields are obligations at the construction site. Once Lean accepts the declaration, callers can use the homomorphism's generic API instead of repeating the proof that the first component of a product respects multiplication.

The identity and composition operations are also bundled. If `f : M →* N` and `g : N →* P`, then their composition is again a monoid homomorphism. This closure is a key reason to use bundled maps: theorems can compose abstract structure-preserving functions without inspecting their implementations.

For more complicated maps, build the function first and state the laws as separate lemmas. Then use those lemmas in the structure fields. This keeps a long algebraic proof separate from the bundle constructor and makes it possible to reuse the preservation theorem elsewhere.

## 3. Use the generic map lemmas

Once a map is bundled, use its generic laws rather than unfold its fields. For a monoid homomorphism, the family of `map_*` theorems handles identity, multiplication, powers, inverses when available, and related operations. The precise set depends on the source and target structures.

This generic interface is often more powerful than a theorem about one specific function. A theorem proved for every `f : M →* N` can be applied to any monoid homomorphism, including maps added by another module. The proof depends on the contract rather than a concrete implementation.

The map laws are commonly registered as simplification rules. A proof can therefore use `simp` to move a homomorphism through an operation:

```lean
example {M N : Type _} [Monoid M] [Monoid N]
    (f : M →* N) (a b : M) : f (a * b) = f a * f b := by
  simp
```

Use explicit `map_mul` when the proof should make the structure-preservation step visible. Use `simp` when several standard map laws and neutral-element rules should be applied together. Chapter 2's simplifier principles still apply: the rewrite should move toward a useful normal form.

The operation's typeclass assumptions determine which law is available. A monoid homomorphism preserves natural powers because powers are built from multiplication and one. A group homomorphism can preserve inverses because inverses exist in the source and target. A function that preserves multiplication but has no proof about order does not become monotone automatically. Read the typeclass requirements of a `map_*` theorem to see exactly which structure it uses.

Bundled maps also compose. If `f` and `g` preserve multiplication, then `g ∘ f` preserves multiplication, and Mathlib provides composition operations whose result remains bundled. This closure supports long chains of abstraction: a proof can reason about the composite map using the same generic law without unfolding either component.

## 4. Equality of bundled maps

Two homomorphisms are equal when their underlying functions agree pointwise, because their proof fields certify propositions and are irrelevant to the mathematical data. An extensionality theorem exposes this principle:

```lean
example {M N : Type _} [Monoid M] [Monoid N]
    (f g : M →* N) (h : ∀ x, f x = g x) : f = g := by
  ext x
  exact h x
```

The `ext` tactic finds an extensionality theorem for the bundled map, then reduces the equality to equality of outputs at an arbitrary input. This is the same proof design as function extensionality from Chapter 4, applied to a structure whose essential data is a function.

When a bundled-map equality goal is difficult, ask what observations determine the structure. For a homomorphism, pointwise outputs are usually sufficient. For a bundled map with additional data, such as a proof of monotonicity or continuity, those proof fields do not add independent mathematical values. If a structure contains computational fields beyond its function, its extensionality theorem may ask you to compare them too.

Prefer the map-specific extensionality theorem to manually destructing the structure. The theorem is a stable abstraction boundary and remains valid if the internal representation changes.

## 5. Structure preservation is separate from injectivity

A homomorphism preserves operations, but it need not be injective or surjective. These properties should be stated separately when the theorem requires them. For example, injectivity lets equality of outputs reflect equality of inputs:

```lean
example {M N : Type _} [Monoid M] [Monoid N] (f : M →* N)
    (hinj : Function.Injective f) {a b : M} (h : f a = f b) : a = b := by
  exact hinj h
```

Surjectivity instead says every target has a preimage. It is useful for transferring existence results from the source to the target, but it does not imply that a chosen preimage is unique. Injectivity and surjectivity solve different proof problems.

When a homomorphism is injective, Mathlib may provide a stronger bundled embedding that combines the function and its injectivity proof. A map that is both bijective and structure-preserving can be packaged as an isomorphism for that structure. These bundles let later theorems inherit the correct combination of properties without repeating hypotheses.

## 6. Choose the weakest map that captures the theorem

The right bundle records exactly the guarantees that downstream results need:

| Mathematical guarantee | Typical interface |
| --- | --- |
| A function only | `α → β` |
| A function with injectivity | `α ↪ β` or a structure-specific embedding |
| A bijection | `α ≃ β` |
| A bijection preserving algebraic operations | A structured equivalence such as `M ≃* N` |
| Preservation of a single operation | The corresponding homomorphism type |
| Preservation of order | An order homomorphism or order isomorphism |

The table is a guide, not a demand to bundle every map. If a property is needed only once, a function plus a local hypothesis may be simpler. If the property will be reused throughout a development, put it in the map's type.

For example, a theorem about preserving a single multiplication may take a raw function together with a proof of the multiplication law. This is appropriate for a local argument. If many theorems use the same function and law, constructing a `MonoidHom` removes repeated hypotheses and lets existing map lemmas apply. The decision is about the expected lifetime and reuse of the interface, not about preferring structures for their own sake.

Do not use a plain equivalence when a later theorem needs multiplication to be preserved; that theorem would have to assume and prove the law separately. Conversely, do not require an isomorphism when only a forward homomorphism is available. The type should express the actual mathematics and no stronger promise.

There is also a difference between proving a map preserves structure and proving two structures are isomorphic. The first is a theorem about a chosen function. The second supplies an inverse map and inverse laws in addition to preservation. Keeping these claims separate helps avoid circular reasoning, such as treating a surjective homomorphism as injective without an additional kernel or cancellation argument.

An isomorphism is therefore evidence of representation equivalence, not just a function with a convenient name. Use its inverse and preservation laws through the bundled API so both directions remain explicit.

## 7. Kernels, ranges, and structural transfer

Bundled homomorphisms connect the behavior of elements with substructures. The kernel collects source elements mapped to the identity; the range collects target elements attained by the map. In many algebraic settings, these are themselves bundled subobjects with closure proofs supplied by the homomorphism laws.

This gives a common proof strategy. To show a homomorphism is injective, analyze its kernel. To show it is surjective, show every target element belongs to its range. To transfer an algebraic property, use the map laws and the induced structure on the image. Mathlib provides these concepts in specialized APIs; use their existing definitions rather than rebuilding sets and closure proofs by hand.

This relationship also suggests a theorem-design choice. If the result is about a map's behavior on every element, state it directly for the homomorphism. If it is about the substructure represented by the image, use the image or range API. If it needs uniqueness of preimages, state injectivity. Each formulation puts the relevant guarantee in the context and avoids proving the same side condition inside every lemma.

When exploring a structure-specific map, inspect both its base homomorphism API and its subobject API. A ring homomorphism may induce maps on ideals, a group homomorphism on subgroups, and an order homomorphism on intervals. These derived constructions often already include the closure proofs required for their target types.

The map type also controls which structure can be transported. An injective ring homomorphism identifies the source with a subring of the target. A ring equivalence identifies the entire structures. A monotone bijection need not preserve addition, so order structure alone does not justify algebraic rewriting. State and use only the preservation laws that follow from the chosen bundle.

## 8. Common failure modes

### A raw function is used where a homomorphism is required

The theorem cannot use preservation laws until they are stated or bundled. If the laws are central to the development, construct a bundled map and use its generic API.

### A homomorphism is assumed to be injective

Structure preservation does not imply injectivity. Supply an injectivity proof or use an embedding when injectivity is part of the theorem.

### An equivalence is mistaken for a structure isomorphism

A bijection need not preserve operations or order. Use the stronger bundled equivalence when those laws are required.

### A map equality is proved by comparing structure fields manually

Try `ext` and the corresponding extensionality theorem. Proof fields do not usually need to be compared by hand.

### The implementation is unfolded to prove a generic fact

Use `map_mul`, `map_pow`, and related map laws. Unfolding couples the proof to one definition and discards the abstraction provided by the bundle.

### A theorem asks for a stronger map than the construction provides

Check which laws the target bundle requires. If the mathematics only supplies an injective homomorphism, do not attempt to fill an isomorphism's inverse fields. State the result for the weaker map or prove the additional surjectivity theorem separately.

## 9. Exercises

1. Define the second projection from a product of monoids as a bundled monoid homomorphism and prove its application equation.
2. Prove that two monoid homomorphisms are equal if they agree on all inputs, using `ext`.
3. Use a homomorphism's generic map laws to prove it preserves powers.
4. Give a homomorphism that is not injective. State which additional bundle would record injectivity.
5. Explain why a bijection between two rings is not automatically a ring equivalence. List the preservation laws that are missing.
6. Choose a bundled map appropriate for a theorem about an additive, order-preserving bijection. Explain which properties the type must encode.
7. Locate a homomorphism in Mathlib that maps between two familiar algebraic structures. Read its constructor fields and one theorem stated using the bundled type.

## Summary

Bundled maps pair functions with proofs of the laws that characterize them. Homomorphisms expose generic `map_*` theorems; extensionality reduces equality of maps to equality on inputs. Preservation of structure is distinct from injectivity and surjectivity, so choose homomorphisms, embeddings, equivalences, or structured isomorphisms according to the guarantees the mathematics provides. Use the bundle's API instead of unfolding its implementation, and bundle reusable properties into the map type when they are central to later results.

## Further reading

- [Mathlib: Algebraic homomorphisms](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Hom/Defs.html)
- [Mathlib: Basic monoid homomorphism APIs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Hom/Basic.html)

end Chapter13
