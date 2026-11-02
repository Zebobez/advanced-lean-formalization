# Chapter 9 — Quotients and Equivalence Relations

> **Audience.** This chapter assumes you know equivalence relations and subtypes. It explains how quotients represent objects up to an equivalence, why functions on quotients require a compatibility proof, and how to reason without choosing arbitrary representatives.

Many mathematical objects are considered identical for a particular purpose even when their concrete representatives differ. Integers can be represented by pairs of natural numbers; rational numbers by pairs with a nonzero denominator; paths can be identified when they are homotopic; and natural numbers can be grouped by their remainder modulo a fixed value. A quotient type packages this “same for our purposes” relation into a new type.

The main discipline is to distinguish equality of representatives from equivalence of representatives. A function defined on a quotient must give the same answer for equivalent inputs. Once that compatibility is proved, Lean's quotient interface provides lifting and induction principles that let a proof use representatives safely.

## Learning objectives

By the end of the chapter, you should be able to:

- define a setoid from a reflexive, symmetric, transitive relation;
- construct a quotient and relate representative equality to quotient equality;
- define a function on quotient classes by proving representative independence;
- use quotient induction for propositions about arbitrary classes;
- avoid proofs that depend on a chosen representative;
- decide when quotienting is a suitable mathematical representation.

## 1. Equivalence is not equality

Let natural numbers be equivalent when they have the same remainder modulo 2:

```lean
namespace Chapter09

def sameParity (a b : Nat) : Prop := a % 2 = b % 2
```

This relation is reflexive, symmetric, and transitive because equality of remainders has those properties. Lean's `Setoid` structure packages the relation with those three proofs:

```lean
def paritySetoid : Setoid Nat where
  r := sameParity
  iseqv := {
    refl := by intro a; rfl
    symm := by intro a b h; exact h.symm
    trans := by intro a b c h₁ h₂; exact h₁.trans h₂
  }

abbrev ParityClass := Quotient paritySetoid
```

The quotient has one class for each parity. The natural numbers `0`, `2`, and `14` are not equal as natural numbers, but they determine the same element of `ParityClass`. The quotient identifies them because the chosen relation says they have the same remainder.

The relation is not merely a convenient theorem predicate. It defines the meaning of equality in the quotient. Choosing the wrong relation changes the objects being represented, so write down the mathematical equivalence before writing the Lean structure.

## 2. Representatives and quotient equality

Each representative maps to a quotient class with `Quotient.mk`. If two representatives are related, their classes are equal:

```lean
theorem parityClass_eq_of_sameParity {a b : Nat} (h : sameParity a b) :
    Quotient.mk paritySetoid a = Quotient.mk paritySetoid b := by
  exact Quotient.sound h
```

This direction is often called soundness: the quotient respects the relation used to construct it. There is a corresponding exactness principle that can recover the relation from equality of classes, but most user-facing proofs should avoid converting back and forth unnecessarily. Work through the quotient's lifting and induction interfaces instead.

For this concrete setoid, the two principles give an exact characterization of class equality:

```lean
theorem parityClass_eq_iff {a b : Nat} :
    Quotient.mk paritySetoid a = Quotient.mk paritySetoid b ↔ sameParity a b := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h
```

The forward implication is exactness: equal classes must come from related representatives. The reverse implication is soundness: related representatives are identified by the quotient. This theorem is useful at boundaries where a proof starts with quotient equality but ultimately needs to reason about the underlying relation.

In the rest of a development, prefer not to unfold the quotient or repeatedly reconstruct this equivalence. Use the characterization when the theorem is genuinely about representatives; use lifted functions when the proof is about values computed from classes. Keeping those interfaces separate makes it clear whether a result depends on the relation or on an operation defined over the quotient.

The quotient constructor maps many representatives to one class:

```text
0 ─┐
2 ─┼──▶ even class
4 ─┘

1 ─┐
3 ─┼──▶ odd class
5 ─┘
```

The diagram is schematic: all natural numbers are grouped according to their remainder, not just the displayed examples. The crucial point is that the quotient value does not retain a distinguished representative as part of its public meaning.

## 3. Defining a function on classes

To define a function from a quotient, first define it on representatives. Then prove it gives equal outputs whenever its inputs are related. For parity, the output can be a `Fin 2` code:

```lean
def parityCode (n : Nat) : Fin 2 :=
  ⟨n % 2, Nat.mod_lt _ (by decide)⟩
```

The relation `sameParity` was chosen precisely so that `parityCode` respects it. We can lift this representative-level function to the quotient:

```lean
def parityOfClass : ParityClass → Fin 2 :=
  Quotient.lift parityCode (by
    intro a b h
    apply Fin.ext
    exact h)
```

The proof after `Quotient.lift` is a compatibility obligation. Given `h : sameParity a b`, it proves `parityCode a = parityCode b`. `Fin.ext` reduces equality of finite indices to equality of their values, which is exactly `h`.

The resulting function does not ask which representative was chosen. Every representative of the same class produces the same parity code:

```lean
@[simp] theorem parityOfClass_mk (n : Nat) :
    parityOfClass (Quotient.mk paritySetoid n) = parityCode n := by
  simp [parityOfClass]
```

This theorem is a useful interface for computations on representatives. A client can simplify the quotient function on a class built from a known natural number without unfolding the quotient implementation.

### The compatibility condition is the mathematical content

Suppose a proposed function on representatives is `f : α → β`. To descend it to a quotient by `r`, the required statement is:

```text
if r a b, then f a = f b
```

If this fails, `f` is not a well-defined function on equivalence classes. This is not a Lean-specific inconvenience; it is the mathematical condition for a function to respect the identification.

For example, the natural-number value itself does not define a function from parity classes to `Nat`: the class of even numbers contains many representatives with different values. The remainder modulo 2 does descend because it is constant on every class. When a lift proof fails, check whether the proposed function is genuinely invariant under the relation.

The lifting pattern is useful enough to write generically:

```lean
def descend {α β : Type _} (s : Setoid α) (f : α → β)
    (hf : ∀ a b, s.r a b → f a = f b) : Quotient s → β :=
  Quotient.lift f hf
```

The setoid is an explicit argument so the caller chooses the intended relation. The function `hf` is the mathematical compatibility theorem. Once it is supplied, the quotient's abstraction barrier guarantees that the result cannot depend on which equivalent representative was used.

This is the quotient's universal property in function form: compatible maps on representatives correspond to maps from the quotient. The lifted map is determined by its behavior on representatives, and its representative equation is what clients should use. For a map into another quotient or a function of several quotient arguments, compatibility must account for each input relation; the library provides corresponding multi-input lifting operations, but the proof obligation remains the same.

## 4. Proving propositions about quotient elements

To prove a proposition about an arbitrary quotient class, quotient induction allows reasoning about a representative. The property must be meaningful for the class, but its proof can often be reduced to the representative case.

For example, every parity class has a representative whose remainder is below 2:

```lean
theorem parityClass_has_small_representative (q : ParityClass) :
    ∃ n : Nat, Quotient.mk paritySetoid n = q ∧ n % 2 < 2 := by
  refine Quotient.inductionOn q ?_
  intro n
  refine ⟨n, rfl, ?_⟩
  omega
```

The proof introduces a representative `n`, uses it as the witness, and proves the bound with arithmetic. The quotient induction principle constructs the result for the original class from the representative case.

For a proposition that is stated through a lifted function, equation lemmas often make the representative case straightforward. Keep the quotient induction step small: establish the mathematical property on a representative, then let the quotient principle transport the proof to its class.

There is an important distinction between proving an existential representative statement and defining a function that extracts a representative. Quotient induction permits representative reasoning inside an appropriate proposition. It does not make a chosen representative canonical. In general, selecting one representative from each equivalence class requires additional choice and may have no useful computational behavior.

## 5. Why representative independence matters

A common failed approach is to write a function by inspecting a quotient element as though it were a pair containing one original value. Quotient abstraction intentionally hides that value. Even if classical choice can select a representative, the choice may differ across equivalent inputs and make a proposed function ill-defined.

Instead, use one of two standard interfaces:

- **Lifting:** define a function on representatives and prove it respects the relation.
- **Quotient induction:** prove a proposition by reducing to a representative case.

Lifting is appropriate when constructing a map out of the quotient. Quotient induction is appropriate for proving a property of every quotient element. Both interfaces require the proof to respect the chosen relation where relevant.

When a target is a proposition, Lean has more freedom to eliminate quotient values than when the target is arbitrary computational data. This distinction reflects proof irrelevance and quotient soundness. For computational output, representative independence must be explicit: Lean must know that different representatives produce equal results.

## 6. Quotients versus subtypes and equivalences

A subtype keeps the underlying value and attaches a predicate proof. A quotient identifies values according to a relation and forgets which representative was used. They solve opposite representation problems:

| Construction | What it records | Typical use |
| --- | --- | --- |
| Subtype `{x : α // p x}` | A chosen value plus evidence of a property | Positive numbers, bounded values |
| Quotient `Quotient s` | An equivalence class under a relation | Integers, residue classes, syntax modulo equations |
| Equivalence `α ≃ β` | A bijection between two types | Changing representation without identifying distinct inputs |

Choose a quotient when the mathematics treats related representatives as one object. Choose a subtype when the actual representative matters and must satisfy an invariant. Choose an equivalence when there is a reversible correspondence and the objects should remain distinguishable.

A quotient can be mathematically elegant but may make computation less direct, because representatives are hidden. Sometimes it is more practical to use a concrete representative structure with a canonicalization function and prove normalization properties. The right choice depends on whether the development needs computation, extensional reasoning, or a faithful model of mathematical equivalence.

## 7. Designing a relation for Lean

Before constructing a `Setoid`, answer four questions:

1. What does it mean for two representatives to describe the same object?
2. Is the relation reflexive, symmetric, and transitive?
3. Which operations should be available on equivalence classes?
4. Do those operations preserve the relation in each argument?

The fourth question anticipates a substantial proof burden. If addition is to be defined on residue classes, changing either representative must leave the sum class unchanged. For an operation with several inputs, prove compatibility in all of them. Bundled structures and Mathlib's quotient APIs can help, but they do not remove the underlying mathematical obligation.

Name the relation for its mathematical meaning, not just its implementation. For a development with multiple equivalence relations on the same type, avoid relying on a global `Setoid` instance unless one relation is truly canonical. Passing the setoid explicitly, as this chapter does, makes the intended quotient unambiguous.

Operations require compatibility in every argument. To define addition on parity classes, for instance, show that replacing either addend with a number of the same parity leaves the sum's parity unchanged. Lean's `Quotient.liftOn₂` expresses this two-input version of the lifting pattern. For a function of three quotient arguments, the compatibility statement must compare all three representative pairs. Writing the mathematical relation first makes these obligations easier to state and prevents an implementation from silently depending on the representatives.

## 8. Common failure modes

### A function does not respect the relation

Check the compatibility obligation with concrete equivalent representatives. If outputs differ, the function cannot descend to the quotient as stated. Change the function, strengthen the relation, or use a different representation.

### Equality of representatives is confused with equality of classes

Different representatives can yield the same quotient element. Use `Quotient.sound` when a relation proves class equality; use quotient induction or an exactness theorem when reasoning in the other direction.

### A proof tries to extract a canonical representative

Quotient elements do not carry a preferred representative. If the mathematics requires one, define and prove a canonicalization operation separately, or choose a representation that stores canonical data.

### A lifted function has an opaque equation

Prove or use its representative equation. The lift's behavior on a class constructor is part of its interface; clients should not unfold the internals of quotient recursion.

### A quotient carries too much implementation overhead

If almost every theorem immediately chooses a representative and reconstructs the same normal form, consider whether a subtype of canonical representatives or an equivalence to a simpler concrete type would serve better.

## 9. Exercises

1. Define a setoid on natural numbers that identifies numbers with equal remainder modulo 3. Prove reflexivity, symmetry, and transitivity.
2. Define a quotient class of integers modulo 2 and lift the parity function to `Fin 2`. State the representative-independence proof explicitly.
3. Prove that if `sameParity a b`, then the quotient classes of `a` and `b` are equal.
4. Give an example of a function on representatives that does not descend to parity classes. Identify a specific related pair that violates compatibility.
5. Prove a proposition about every quotient class by quotient induction. Explain why this proof does not define a canonical representative function.
6. Compare a quotient by an equivalence relation with a subtype of canonical representatives. List one advantage and one cost of each representation for a computational development.

## Summary

A quotient represents objects up to a chosen equivalence relation. A `Setoid` packages that relation with reflexivity, symmetry, and transitivity; `Quotient.sound` turns related representatives into equal classes. A function on classes must be proved independent of representatives before it can be lifted. Quotient induction supports representative-based proofs of propositions, while computational maps require an explicit compatibility law. Use quotients when the relation expresses genuine mathematical identity for the development, and consider subtypes or equivalences when preserving concrete representatives is more useful.

## Further reading

- [Lean reference: Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/)
- [Theorem Proving in Lean 4: Axioms and Computation](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/)

end Chapter09
