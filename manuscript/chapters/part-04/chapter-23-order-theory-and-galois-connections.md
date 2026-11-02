# Chapter 23 — Order Theory and Galois Connections

> **Audience.** This chapter assumes familiarity with partial orders, lattices, and bundled homomorphisms. It shows how Mathlib's order interfaces package monotonicity, how Galois connections turn proof goals into equivalent inequalities, and why adjoints preserve particular lattice operations.

Order-theoretic formalization rewards a shift from element-by-element calculations to structure-preserving maps. Once monotonicity, closure, and adjunctions are stated through their standard interfaces, many theorems follow from generic order lemmas. This chapter develops a useful path from an unbundled function to an `OrderHom`, then from a pair of monotone maps to a `GaloisConnection`.

The central practice is to use the order relation that the structures already provide. Prove inequalities instead of equalities when the order theory naturally gives bounds. State an adjunction once, then apply its equivalence in both directions rather than repeating the same elementwise reasoning.

## Learning objectives

By the end of the chapter, you should be able to:

- use `Monotone` and `OrderHom` to expose order-preserving behavior;
- prove that image and preimage form a Galois connection;
- use the adjunction equivalence to move inequalities across maps;
- recognize the unit and counit inequalities of a Galois connection;
- exploit the join-preserving and meet-preserving behavior of adjoints.

## 1. Monotonicity is an interface

A function `f : α → β` between preorders is monotone when it preserves the order relation: if `a ≤ b`, then `f a ≤ f b`. In Lean, `Monotone f` records this property as a function from an inequality to an inequality. It is frequently a hypothesis to a theorem, a field in a bundled map, or a proof obligation after defining a new operation.

For example, successor on natural numbers is monotone:

```lean
example : Monotone (fun n : Nat => n + 1) := by
  intro a b hab
  exact Nat.add_le_add_right hab 1
```

The proof is intentionally stated in terms of the interface. It does not unfold the definition of natural-number addition and manually analyze constructors. `omega` discharges the linear arithmetic consequence. In a library theorem, using the `Monotone` predicate makes the result compose with other order-theoretic lemmas.

When a function and its monotonicity will be reused together, bundle them in an `OrderHom`:

```lean
def succOrderHom : Nat →o Nat where
  toFun n := n + 1
  monotone' := by
    intro a b hab
    exact Nat.add_le_add_right hab 1
```

The notation `α →o β` denotes bundled monotone maps. An `OrderHom` coerces to a function, so ordinary application remains concise, while the monotonicity proof is carried with the map. This mirrors the bundled map design from Chapter 13. If monotonicity is needed only once, an unbundled `Monotone` theorem may be enough; if it is a stable part of the object, bundle it.

## 2. Work with the order relation, not its implementation

Many types in Mathlib have a partial order induced by inclusion. For sets, `s ≤ t` is equivalent to `s ⊆ t`. For subgroups, submodules, filters, and other structured collections, the order often expresses containment or refinement. Generic lemmas can apply without knowing the element-level details.

One fundamental example comes from any function `f : α → β`. Sending a set to its image and a set to its preimage reverses direction in a precise way:

```lean
theorem imagePreimageGC {α β : Type*} (f : α → β) :
    GaloisConnection
      (fun s : Set α => f '' s)
      (fun t : Set β => f ⁻¹' t) := by
  intro s t
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h hx
```

The first direction says that if the image of `s` is contained in `t`, then every `x` in `s` maps into `t`. The second direction says that if every point of `s` maps into `t`, then every point of the image lies in `t`. The proof is ordinary set reasoning, but the final proposition is reusable as an adjunction.

Once this relationship is established, later proofs should use the Galois connection rather than repeat the witness manipulation. The abstraction has compressed a recurring proof pattern into an order equivalence.

## 3. The adjunction equivalence

A Galois connection between preorders consists of a lower map `l : α → β` and an upper map `u : β → α` satisfying:

\[
  l(a) \le b \quad\Longleftrightarrow\quad a \le u(b).
\]

In Lean, `GaloisConnection l u` packages exactly this condition. Given `gc : GaloisConnection l u`, applying `gc a b` yields the equivalence at particular values:

```lean
example {α β : Type*} [Preorder α] [Preorder β]
    {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) (a : α) (b : β) :
    l a ≤ b ↔ a ≤ u b := by
  exact gc a b
```

This equivalence is the central API. If the target has the shape `l a ≤ b`, use the forward direction to obtain `a ≤ u b`. If the hypotheses contain `a ≤ u b`, use the reverse direction to prove `l a ≤ b`. The lower and upper maps can have different domains, so a goal's type often tells you which side of the adjunction to use.

Lean's library also provides named theorems such as `GaloisConnection.le_iff_le`, `GaloisConnection.l_le`, and `GaloisConnection.le_u`. The direct application `gc a b` is often sufficient; named lemmas can be clearer when a longer proof has several adjunctions in scope. Check the inferred argument order with `#check` rather than relying on memory.

The relation supplies monotonicity of both maps and two useful inequalities, often called the unit and counit:

```text
a ≤ u (l a)          l (u b) ≤ b
      unit                 counit
```

These bounds say that composing lower then upper approximates an element from above, while composing upper then lower approximates an element from below. They are not necessarily equalities. When one composite is equal to the identity, the connection has the stronger structure of an insertion or coinsertion.

The defining equivalence also explains monotonicity. If `a ≤ a'`, the unit gives `a' ≤ u (l a')`; transitivity then gives `a ≤ u (l a')`, which the adjunction converts to `l a ≤ l a'`. For the upper map, if `b ≤ b'`, the counit gives `l (u b) ≤ b ≤ b'`; the adjunction converts this to `u b ≤ u b'`. The library packages these consequences so clients do not need to derive them repeatedly. When constructing a connection from simpler monotonicity and approximation facts, use the introduction theorem provided by Mathlib rather than reproving the equivalence for each pair of inputs.

An adjunction is not generally an inverse pair. For image and preimage, distinct source sets can have the same image, and not every target set is the image of a source set. The connection still holds because it describes how inequalities correspond, not a bijection between elements. This distinction prevents a common mistake: do not replace the unit and counit inequalities by equalities unless the construction has an insertion, coinsertion, or order isomorphism property.

## 4. Closure and inclusion form a standard example

Let `S` be a collection of subsets of an ordered or algebraic object that satisfy a closure property. The closure operation sends arbitrary subsets to the smallest closed object containing them. The inclusion map forgets the extra structure and remembers the underlying set. These maps form an adjunction: the closure of a set lies in a closed object precisely when the original set already lies in that object.

For subgroups, the lower map sends a set to the subgroup it generates, and the upper map sends a subgroup to its carrier set. The Galois connection packages:

```text
generated subgroup of S ⊆ H   ↔   S ⊆ carrier of H
```

This equivalence is far more useful than a standalone monotonicity theorem. It says what closure means through its universal property. A proof that a generated subgroup is contained in `H` becomes a proof that the generators lie in `H`. A proof that all elements of `S` are included in the carrier gives the reverse implication.

Mathlib uses Galois insertions to lift order structure from a representation to a structured subtype. A Galois insertion strengthens the adjunction with a retraction law, allowing lattice operations on the structured side to be defined without repeatedly applying closure. This is why the standard subgroup infimum can be set intersection directly: the intersection is already a subgroup. The generic connection supports the transfer, and the insertion data preserves the efficient representation.

Another way to recognize closure is by its fixed points. A closure operator is typically monotone, extensive, and idempotent: `a ≤ c a`, `c (c a) = c a`, and order preservation. Its fixed points are precisely the closed objects. The inclusion of fixed points into the ambient order often has a Galois connection with the closure map. This perspective lets one prove facts about all closed objects through the universal property of closure rather than by inspecting a construction's algorithm.

When a structure is defined by a universal property such as “smallest object containing these generators,” look for a Galois connection. It is often the best statement of the construction's API.

## 5. Adjoints preserve joins and meets

When the order structures have suprema and infima, a lower adjoint preserves suprema and an upper adjoint preserves infima. For example, if `l` is the lower map of a Galois connection, then applying `l` to a supremum is equivalent to taking the supremum of the images. Dually, `u` preserves infima.

```text
l (a₁ ⊔ a₂) = l a₁ ⊔ l a₂       lower adjoint preserves joins
u (b₁ ⊓ b₂) = u b₁ ⊓ u b₂       upper adjoint preserves meets
```

These equalities are consequences of the defining order equivalence, not extra hypotheses. The proof compares both sides by their universal properties as least upper bounds or greatest lower bounds. For complete lattices, the same reasoning applies to arbitrary suprema and infima, including indexed families.

The preservation direction is easy to reverse by accident. If a function is a left adjoint, it preserves joins; if it is a right adjoint, it preserves meets. A map that preserves both joins and meets may be an order isomorphism, but one-sided preservation is enough to characterize many constructions.

This matters in proofs involving arbitrary unions, generated objects, closure, or limits of approximations. Instead of unfolding the construction, rewrite through its adjunction and use a generic theorem about suprema or infima. If an expected equality is unavailable, check whether you have the correct adjoint orientation or whether only an inequality follows.

In a concrete proof, the transfer often has a short shape. To show that the lower image of a supremum is below some `b`, use the adjunction to turn the goal into an inequality in the source order. The universal property of the supremum handles each input there. Then transfer back if the desired conclusion is stated in the target. The same idea works with infima on the upper map. Writing the two order domains beside the maps is a useful safeguard against applying a theorem at the wrong type.

## 6. Monotone maps and order homs in proof design

An `OrderHom` carries a function together with monotonicity. It should be used when the map is an object of the theorem: composing monotone maps, comparing maps pointwise, or building a lattice of maps. An ordinary function plus a local `Monotone` hypothesis is often more convenient for one-off statements.

The distinction is similar to bundled homomorphisms in algebra. Bundling records the property once, lets typeclass or coercion infrastructure expose generic operations, and reduces repeated hypotheses. But it also commits the API to a named structure and its coercions. Use the bundled form when clients need the map as structured data; otherwise avoid wrapping a temporary function just to state one theorem.

When a proof goal involves pointwise order between maps, remember that the order on an order-hom type is usually defined pointwise. The pointwise inequality can be reduced to scalar inequalities by applying it at an arbitrary input. Conversely, a theorem about all inputs can build the pointwise order relation. Use `funext` when the goal is equality of functions; use pointwise order when the mathematics only compares values.

For a Galois connection, resist the temptation to unfold the definition at every use. Name the connection and apply its equivalence. If the proof repeatedly changes direction, make the local facts visible:

```lean
example {α β : Type*} [Preorder α] [Preorder β]
    {l : α → β} {u : β → α} (gc : GaloisConnection l u)
    {a : α} {b : β} (h₁ : l a ≤ b) : a ≤ u b := by
  have h₂ : a ≤ u b := (gc a b).mp h₁
  exact h₂
```

The exact syntax of the direction can vary with whether `gc` is written as a function or accessed through a named theorem. The important point is to let the adjunction provide the conversion, not a second hand-written set argument.

## 7. Common failure modes

### The two maps are supplied in the wrong order

Check the defining statement: `GaloisConnection l u` means `l a ≤ b ↔ a ≤ u b`. The lower map comes first. Write the elementwise equivalence before constructing the declaration.

### A proof establishes equality where only an inequality is expected

The unit and counit of a connection are generally inequalities. Equality requires the stronger insertion, coinsertion, or equivalence assumptions.

### A left adjoint is expected to preserve meets

Lower adjoints preserve suprema; upper adjoints preserve infima. Reverse the expectation only if additional structure proves it.

### A monotonicity proof unfolds an operation unnecessarily

Use the existing `Monotone` theorem or an order-hom composition lemma. If the operation is arithmetic, let an arithmetic tactic discharge the local inequality after the order structure is exposed.

### Set reasoning is repeated after an adjunction is available

Use the Galois connection at the point where inclusion changes sides. Rebuilding image witnesses is useful once to prove the connection, but it is noise in every later application.

## 8. A workflow for order-theoretic formalization

1. Identify the preorder or lattice on each type and confirm what `≤` means.
2. State the map's monotonicity using `Monotone`; bundle it as `OrderHom` if clients need the map with its property.
3. For a closure or representation map, look for a universal property of the form `l a ≤ b ↔ a ≤ u b`.
4. Prove the Galois connection from elementwise reasoning once.
5. Use the adjunction to move later goals between the two orders.
6. Apply join or meet preservation in the correct direction.
7. Strengthen to an insertion only when one composite is genuinely the identity.

This workflow is effective because it separates the construction-specific proof from the order-generic consequences. It also gives theorem search recognizable names and structures to find.

## 9. Exercises

1. Define an `OrderHom` on `Nat` for doubling and prove its monotonicity. Compare it with a theorem whose function is unbundled.
2. Prove that image and preimage form a Galois connection. Then use the connection to prove an inclusion without constructing image witnesses again.
3. State the unit and counit inequalities for the image-preimage connection and interpret each in terms of sets.
4. Explain why subgroup closure and coercion to carrier sets form a Galois insertion. Which direction is closure, and which is forgetting structure?
5. Prove that a left adjoint preserves a binary supremum by comparing least upper bounds. Identify where the adjunction equivalence is used.
6. Find a proof where a monotonicity hypothesis is used repeatedly. Rewrite the API with an `OrderHom` and explain whether bundling improves its clients.
7. Give an example of a map that preserves joins but not meets, or vice versa, and explain why this is consistent with being one side of an adjunction.

## 10. Formalized exercise patterns

The following proofs turn several exercises into reusable statements. They show where an abstraction saves work: first package monotonicity or the adjunction, then apply the resulting interface to later goals.

### Doubling as a bundled monotone map

```lean
def doubleOrderHom : Nat →o Nat where
  toFun n := 2 * n
  monotone' := by
    intro a b hab
    exact Nat.mul_le_mul_left 2 hab

theorem exercise_23_1_unbundled {a b : Nat} (hab : a ≤ b) :
    2 * a ≤ 2 * b := by
  exact doubleOrderHom.monotone hab
```

The final theorem states the same consequence with an unbundled input inequality. The bundled map is useful when its monotonicity is reused across several results; a one-off proof can instead apply `Nat.mul_le_mul_left` directly.

### Moving an inclusion through image and preimage

```lean
theorem exercise_23_2_image_subset_preimage
    {α β : Type*} (f : α → β) (s : Set α) (t : Set β)
    (h : f '' s ⊆ t) : s ⊆ f ⁻¹' t := by
  exact (imagePreimageGC f s t).mp h
```

The witness reasoning is confined to `imagePreimageGC`. Once the connection is named, the inclusion follows by applying one direction of its equivalence.

### Unit and counit for image and preimage

```lean
theorem exercise_23_3_unit
    {α β : Type*} (f : α → β) (s : Set α) :
    s ⊆ f ⁻¹' (f '' s) := by
  exact (imagePreimageGC f s (f '' s)).mp Set.Subset.rfl

theorem exercise_23_3_counit
    {α β : Type*} (f : α → β) (t : Set β) :
    f '' (f ⁻¹' t) ⊆ t := by
  exact (imagePreimageGC f (f ⁻¹' t) t).mpr Set.Subset.rfl
```

The unit says every source point belongs to the preimage of its image. The counit says that mapping back the preimage of a target set cannot add target points.

### A left adjoint preserves binary suprema

```lean
theorem exercise_23_5_left_adjoint_preserves_sup
    {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    {l : α → β} {u : β → α} (gc : GaloisConnection l u)
    (a b : α) : l (a ⊔ b) = l a ⊔ l b := by
  apply le_antisymm
  · apply gc.l_le
    apply sup_le
    · exact (gc a (l a ⊔ l b)).mp le_sup_left
    · exact (gc b (l a ⊔ l b)).mp le_sup_right
  · exact sup_le (gc.monotone_l le_sup_left) (gc.monotone_l le_sup_right)
```

For the first inequality, the adjunction turns the desired target bound into two source bounds, which the supremum property proves. For the reverse inequality, monotonicity sends each input bound through the lower map.

### A join-preserving map need not preserve meets

The direct-image map on sets induced by the constant function from `Nat` to `Unit` is a left adjoint, so it preserves joins. It does not preserve the intersection of the distinct singleton sets below: their intersection is empty, while both images are the singleton of `()`.

```lean
example (s t : Set Nat) :
    (fun _ : Nat => ()) '' (s ∪ t) =
      ((fun _ : Nat => ()) '' s ∪ (fun _ : Nat => ()) '' t) := by
  exact Set.image_union _ _ _

example :
    (fun _ : Nat => ()) '' ({0} ∩ {1} : Set Nat) ≠
      ((fun _ : Nat => ()) '' ({0} : Set Nat) ∩
       (fun _ : Nat => ()) '' ({1} : Set Nat)) := by
  intro h
  have hmem : () ∈
      ((fun _ : Nat => ()) '' ({0} : Set Nat) ∩
       (fun _ : Nat => ()) '' ({1} : Set Nat)) := by
    simp
  rw [← h] at hmem
  simp at hmem
```

## Summary

Use `Monotone` for order-preserving functions and `OrderHom` when monotonicity belongs to the map's reusable interface. A Galois connection packages the equivalence `l a ≤ b ↔ a ≤ u b`; use it to move inequalities between orders. Its unit and counit are generally inequalities, while insertions add a retraction law. Lower adjoints preserve suprema and upper adjoints preserve infima. Prove the connection once, then rely on its generic consequences.

## Further reading

- [Mathlib: Galois connections and insertions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/GaloisConnection/Defs.html)
- [Mathlib: Basic Galois connection theorems](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/GaloisConnection/Basic.html)
- [Mathlib: Bundled order homomorphisms](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Hom/Basic.html)
