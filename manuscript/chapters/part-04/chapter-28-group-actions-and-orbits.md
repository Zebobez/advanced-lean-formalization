# Chapter 28 — Group Actions, Orbits, and Stabilizers

> **Audience.** This chapter assumes familiarity with groups, group actions, equivalence relations, and finite cardinality arguments. It shows how Mathlib packages actions, how to work with orbit and stabilizer interfaces, and how the orbit–stabilizer theorem turns action data into a cardinality calculation.

Group actions are a useful example of a mathematical structure whose laws should be supplied once and used through a broad library API. After Lean knows that a group acts on a type, generic theorems provide orbits, stabilizers, fixed points, transitivity, and quotient constructions. The proof engineer's job is to choose the right object: a pointwise equation, a subset, a subgroup, or a quotient.

The central workflow is to translate an orbit statement into an existential equation only at the point where the witness matters. For global counting, use the orbit–stabilizer equivalence or theorem instead of manipulating group elements and cosets repeatedly.

## Learning objectives

By the end of the chapter, you should be able to:

- read the typeclass assumptions in a `MulAction`;
- move between an orbit and its existential membership criterion;
- treat stabilizers as subgroups and orbits as invariant sets;
- understand orbit–stabilizer as a quotient equivalence and a finite cardinality theorem;
- use transitivity and conjugation actions through the library interface.

## 1. A group action is supplied as structure

A group action on a type `X` is represented by a `MulAction G X` instance. The instance provides scalar notation `g • x` and laws for the identity and multiplication in `G`. The action need not be faithful: different group elements may act in the same way.

```lean
example {G X : Type*} [Group G] [MulAction G X]
    (a x : X) :
    x ∈ MulAction.orbit G a ↔ ∃ g : G, g • a = x := by
  exact MulAction.mem_orbit_iff
```

The typeclass assumption is the API boundary. The theorem does not require a concrete action implementation; it applies to any group and type with the required instance. If Lean reports that `MulAction G X` cannot be synthesized, the issue is usually an unavailable action instance or an action that has not been packaged yet, not a need to reprove the action laws in each theorem.

There are also additive action interfaces for additive groups and additive monoids. The mathematical structure is analogous, with `g +ᵥ x` instead of `g • x`. Use the action type that matches the problem's notation and preserve the library's bundled law rather than translating it into a custom predicate.

## 2. Orbits are subsets with an existential interface

The orbit of `a` is the set of points reachable by acting on `a`. Its membership theorem exposes the witness:

```lean
example {G X : Type*} [Group G] [MulAction G X]
    (a : X) : a ∈ MulAction.orbit G a := by
  rw [MulAction.mem_orbit_iff]
  exact ⟨1, one_smul G a⟩
```

The proof uses the identity element as a witness. For a general membership goal, rewrite with `MulAction.mem_orbit_iff`, then use the group action equation that gives the desired point. Conversely, if a point is written as `g • a`, the same theorem supplies its membership in the orbit.

Orbits are invariant under the action: acting on an orbit produces the same orbit. The orbit itself is also a transitive `G`-set under the restricted action. These facts support two common proof styles:

- work directly with membership witnesses in the ambient type;
- treat the orbit as a subtype and use transitivity on that subtype.

Use the ambient set when the proof compares several orbits or talks about inclusion. Use the subtype when the theorem concerns the orbit as an object on which the group acts.

## 3. Stabilizers are subgroups

The stabilizer of `a` is the subgroup of elements fixing it:

\[
  \operatorname{Stab}_G(a) = \{g \in G \mid g \mathbin{\bullet} a = a\}.
\]

Because it is a `Subgroup G`, it already carries closure under identity, multiplication, and inverses. Membership is reduced to the fixed-point equation through the standard stabilizer membership theorem. As with kernels in Chapter 25, do not unfold the carrier unless the local proof genuinely needs the defining equation.

If a subgroup `H` acts on a point, the statement that every element fixes that point can be recorded as `H ≤ stabilizer G a`. This order-theoretic form is better for combining subgroup hypotheses. A point fixed by all of `G` belongs to `MulAction.fixedPoints G X`, another set-like interface provided by Mathlib.

The action is faithful when the only element acting trivially everywhere is the identity. The stabilizer of one point need not be trivial, so do not confuse pointwise freedom with faithfulness. Freeness requires trivial stabilizers at each point; faithfulness concerns the kernel of the action as a homomorphism into permutations.

## 4. Equivariance preserves orbit structure

A map between two `G`-actions is equivariant when applying the group action before or after the map gives the same result. Such maps send orbits into orbits. If the map is surjective, transitivity can often be transferred from the source to the target.

This is the action analogue of a homomorphism preserving operations. The law should be packaged in an equivariant-map structure when it is reused, rather than restated as a hypothesis for every theorem. Generic lemmas can then reason about the image, kernel-like behavior, and transitivity of the action.

When proving a set inclusion about orbits under an equivariant map, use the orbit membership witness and move the group action across the map using equivariance. The calculation is short, but the named map structure preserves it as an API fact. If the source and target actions are different, make the group homomorphism translating the actions explicit; the equivariance statement then explains how scalars are transported.

For example, a linear map between two representations of the same group is usually studied through its compatibility with the group action. The underlying function may preserve addition and scalar multiplication, while equivariance adds a second equation involving `g • x`. Keeping those properties in their respective bundled interfaces lets a proof use both the linear-map API and the action API without replacing either with a custom record of fields.

When the map is injective, distinct points in an orbit remain distinct in the image, so orbit information can often be reflected back to the source. When the map is surjective, every target point has a preimage, and an orbit argument in the source can establish reachability in the target. These are separate uses of injectivity and surjectivity; equivariance alone only guarantees that acting and mapping commute.

## 5. Orbit–stabilizer is a quotient statement

Fix `a : X`. The map `g ↦ g • a` sends the group onto the orbit. Two group elements have the same image precisely when their difference, in the appropriate multiplication order, belongs to the stabilizer. Thus the orbit is equivalent to the group modulo the stabilizer:

```text
group elements ── g ↦ g • a ──▶ orbit of a
      │                            ▲
      └── identify by stabilizer ──┘
```

Mathlib provides this as `MulAction.orbit_equiv_quotient_stabilizer`. This quotient equivalence is the conceptual orbit–stabilizer theorem. It can be used even before counting, for example to transfer algebraic or finite structure to the orbit.

The proof has two mathematical parts. Surjectivity is the definition of orbit membership. The equivalence relation on group elements is described by the stabilizer. The quotient removes exactly the redundancy in choosing a group element that sends `a` to a target point.

Avoid building this quotient equivalence from scratch unless the action has a specialized relation. The library theorem has already resolved the orientation of cosets and the well-definedness proof. Use the membership characterization to understand the map, then rely on the packaged equivalence in later arguments.

## 6. Finite orbit–stabilizer counting

When the group, orbit, and stabilizer are finite, the equivalence gives the familiar cardinality identity:

\[
  |\operatorname{Orbit}_G(a)|\,|\operatorname{Stab}_G(a)| = |G|.
\]

The corresponding Mathlib theorem is `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`. It expects `Fintype` instances for the group, the orbit subtype, and the stabilizer subtype. A finite group action on a finite type usually provides the latter finiteness facts, but Lean may need the instances to be made explicit.

```lean
example {G X : Type*} [Group G] [MulAction G X] (a : X)
    [Fintype G]
    [Fintype ↥(MulAction.orbit G a)]
    [Fintype ↥(MulAction.stabilizer G a)] :
    Fintype.card ↥(MulAction.orbit G a) *
      Fintype.card ↥(MulAction.stabilizer G a) = Fintype.card G := by
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G a
```

This theorem is an efficient endpoint for counting proofs. If the task is to count the orbit, it may be easier to count the group and stabilizer. If the task is to count the stabilizer, it may be easier to find the orbit. The formal theorem records the exact relation so algebraic rearrangement can happen afterward using `Nat` arithmetic.

Do not infer that an action is transitive just because the orbit of one point has a particular size unless the ambient type is known to have that same finite cardinality. Cardinality equality must be connected to set equality or surjectivity through an additional theorem.

The regular left action of a group on itself is a useful check on the formula. The orbit of the identity is all of `G`, because any `g` sends `1` to `g`. Its stabilizer is the trivial subgroup, because `g * 1 = 1` forces `g = 1`. Orbit–stabilizer then reduces to the identity `|G| · 1 = |G|`. This example is a good way to detect whether a cardinality statement accidentally counts the ambient type, an orbit subtype, or a quotient by a stabilizer.

In a finite action, the theorem is often an intermediate step rather than the final result. It can convert an orbit count into a subgroup count, classify possible orbit sizes, or prove divisibility constraints on a finite group order. For a conjugation action, orbit sizes are conjugacy-class sizes and stabilizers are centralizers. Summing these class sizes partitions the group and leads to the class equation; the pointwise action APIs therefore connect directly to global counting arguments.

## 7. Transitivity and quotienting the action

An action is transitive when any point can be reached from any other. Mathlib expresses pretransitivity as a typeclass `MulAction.IsPretransitive G X`; a separate nonemptiness assumption distinguishes a transitive action on an inhabited type.

The interface provides lemmas to obtain a group element carrying one point to another. Conversely, if one point's orbit is the whole type, the action is pretransitive. This turns orbit calculations into a route to transitivity proofs.

The distinction between an action structure and transitivity is intentional. `MulAction G X` supplies how each group element acts and the compatibility laws. Pretransitivity is an additional proposition about reachability between every pair of points. An action may be perfectly valid while splitting the space into many orbits. This separation allows the same action to support theorems that apply whether or not it is transitive.

The orbit relation partitions `X` into disjoint orbits, and the quotient by that relation is the space of orbits. When the group acts on itself by conjugation, the orbits are conjugacy classes and the stabilizer of an element is its centralizer. This is a particularly useful application: class equations and conjugacy arguments become instances of generic action theorems.

If a quotient action is needed, check whether the subgroup is normal or whether the action descends through a quotient-action instance. A group quotient and an orbit quotient are different constructions. The former quotients the group by a normal subgroup; the latter identifies points related by the action. Keeping the carriers and relations distinct prevents type confusion.

Conjugation also illustrates how stabilizers change along an orbit. If `b = g • a`, then an element fixes `b` exactly when its conjugate by `g⁻¹` fixes `a`. Thus the two stabilizers are conjugate subgroups and have the same cardinality when finite. This explains why all points in a single conjugacy class have centralizers of equal size, even though points in different classes may have different stabilizers.

## 8. Common failure modes

### Orbit membership is unfolded as a set range

Use `MulAction.mem_orbit_iff` to obtain or supply the acting element. The range definition is useful for understanding the object, but the theorem is the client-facing interface.

### A stabilizer is treated as a set only

Use its subgroup order and lattice operations when possible. Membership reduces to a fixed-point equation through the standard lemma.

### The action instance cannot be synthesized

Check the group or monoid type and the action structure. If the action is new, define one instance once with the correct laws; do not re-prove those laws in each orbit theorem.

### Orbit–stabilizer cardinality has missing `Fintype` instances

Make the finite structure on the orbit and stabilizer explicit or derive it from the ambient finite action. The theorem counts subtype elements, not raw set expressions.

### A quotient is confused with a quotient group

Identify whether the relation is on points or on group elements. An orbit quotient does not automatically carry a group operation.

## 9. A workflow for action arguments

1. State the group or monoid and the action instance in the theorem context.
2. Convert orbit membership with `MulAction.mem_orbit_iff` only when a witness is needed.
3. Use the stabilizer subgroup and its order for global fixed-point properties.
4. Package equivariance if a map between actions is reused.
5. Use the quotient equivalence when the theorem concerns orbit structure.
6. Apply the finite cardinality theorem only after the relevant `Fintype` instances are available.
7. For conjugation, use the action API and identify stabilizers with centralizers through library lemmas.

This keeps the proof at the highest useful abstraction. Element calculations establish local facts; subgroups and quotients express global structure; cardinality theorems finish the finite argument.

## 10. Exercises

1. Prove that `a` belongs to its own orbit using the identity element and `MulAction.mem_orbit_iff`.
2. Show that if `x = g • a`, then `x` belongs to the orbit of `a`. Then prove the converse from orbit membership.
3. State the stabilizer of a point as a subgroup and use its membership characterization to prove that a subgroup fixes that point exactly when it lies below the stabilizer.
4. Use `MulAction.orbit_equiv_quotient_stabilizer` to explain why the orbit size equals the number of cosets of the stabilizer in a finite group.
5. Apply the finite orbit–stabilizer theorem to a group action on a finite type. List the exact `Fintype` instances needed.
6. Formalize the regular left action of a group on itself. Identify the orbit and stabilizer of the identity element.
7. Consider the conjugation action of a group on itself. Explain why its orbits are conjugacy classes and its stabilizers are centralizers.

## Summary

`MulAction G X` packages the action laws. Orbits are sets with an existential membership theorem, and stabilizers are subgroups defined by fixed-point equations. The orbit is equivalent to the group quotient by a point's stabilizer; in finite settings this yields the orbit–stabilizer cardinality identity. Use equivariance for maps between actions, pretransitivity for reachability, and the action API for conjugation and quotient arguments.

## Further reading

- [Mathlib: Group action definitions, orbits, and stabilizers](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Defs.html)
- [Mathlib: Orbit–stabilizer and action quotients](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Quotient.html)
- [Mathlib: Pretransitive actions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Action/Pretransitive.html)
