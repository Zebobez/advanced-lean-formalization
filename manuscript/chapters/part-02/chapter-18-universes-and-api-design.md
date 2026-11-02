# Chapter 18 — Universe Polymorphism and API Design

> **Audience.** This chapter assumes comfort with polymorphic definitions, structures, and typeclass-based APIs. It explains how Lean's universe levels affect generic declarations, how to read universe errors, and how to design definitions that remain reusable across types and propositions.

Most Lean code does not need explicit universe annotations. Lean infers universe parameters for ordinary polymorphic definitions, just as it infers many type arguments. The difficulty appears when a declaration is more general than the standard `Type` universe, when two APIs compose across levels, or when an error reports a mismatch involving `Type 1`, `Sort`, or `max`. Understanding the small amount of structure behind these messages makes universe errors tractable.

## Learning objectives

By the end of the chapter, you should be able to:

- explain the relationship among `Prop`, `Sort u`, and `Type u`;
- recognize implicit universe polymorphism in definitions and structures;
- read universe levels in function and product types;
- decide whether a parameter should range over `Type u` or `Sort u`;
- diagnose common universe mismatch errors without reflexively inserting `ULift`.

## 1. Types live in universes

Lean stratifies types into a hierarchy of sorts. The notation `Sort u` denotes the sort at universe level `u`. Propositions occupy `Sort 0`, written `Prop`, and data types at level `u` occupy `Sort (u + 1)`, written `Type u`.

```text
Sort 0       = Prop
Sort 1       = Type 0 = Type
Sort 2       = Type 1
Sort 3       = Type 2
    ⋮
Sort (u+1)   = Type u
```

This hierarchy avoids the paradox that would arise if a type could contain itself without restriction. The universe of a type is a level attached to that type; it is not a size estimate for values. A `Nat` and a large finite structure are both in `Type 0`. Moving to a higher universe is about what kinds of types a declaration can contain, not about runtime memory or mathematical magnitude.

The familiar identity function is polymorphic both in the type it accepts and in the universe where that type lives:

```lean
universe u

def idSort {α : Sort u} (x : α) : α := x

#check idSort
```

The printed result includes a universe parameter `u`; Lean can instantiate it at different levels. The definition works for a proposition as the type `α` as well as for ordinary data types, because its parameter uses `Sort u`. In everyday code, the built-in `id` already has this generality.

## 2. Universe polymorphism is a second kind of polymorphism

Type polymorphism lets one declaration work for multiple types of the same universe shape. Universe polymorphism lets it work when those types live at different levels. Consider a wrapper that stores one value:

```lean
universe u

structure Box (α : Type u) where
  value : α

def Box.extract {α : Type u} (b : Box α) : α := b.value
```

The type `Box α` belongs to a universe determined by the universe of `α`. There is not a separate `BoxAtLevelZero`, `BoxAtLevelOne`, and `BoxAtLevelTwo`; the one declaration can be instantiated at each needed level. This is the usual design for generic containers.

Universe parameters are inferred from a declaration's type in much the same way as type parameters. The `universe` command names levels so a family of declarations can refer to them explicitly. It is useful when an annotation makes a signature clearer or when several declarations must share the same level variable. It is not normally necessary to annotate every polymorphic function by hand.

The universes of inputs and outputs need not be equal. A function can map from one type level to another:

```lean
universe u v

def mapPair {α : Type u} {β : Type v} (f : α → β)
    (pair : α × α) : β × β :=
  (f pair.1, f pair.2)
```

The product type can contain components from different universes. Its universe is chosen to be large enough for both components. This is a recurring pattern: the resulting universe level is often a maximum of the levels required by its fields or arguments.

## 3. `Type` and `Sort` express different API promises

Use `Type u` when a declaration expects data types. This is the common choice for containers, algebraic structures, and computational functions. Use `Sort u` when the operation is meaningful for propositions as well as data types, or when a foundational API genuinely ranges over arbitrary sorts.

```lean
universe u

def keepType {α : Type u} (x : α) : α := x
def keepSort {α : Sort u} (x : α) : α := x
```

`keepSort` accepts `α = Prop` in a way that `keepType` does not. That extra generality is valuable for identity-like operations, logical encodings, and some generic type constructors. It is not free: elimination from propositions is restricted in ways that preserve proof irrelevance and consistency. A declaration that only works for data should say so through `Type`; replacing every `Type` with `Sort` can expose cases its implementation cannot eliminate.

There is a design question here, not just an inference trick. A generic transformation on arbitrary types may naturally use `Sort`. A container of values, a finite map, or an algebraic carrier usually wants `Type`. Keep the parameter as narrow as the mathematics and computation require. Over-general signatures can create confusing constraints and may rule out elimination patterns needed by the implementation.

### Propositions as results

Functions returning propositions are still ordinary Lean functions. If `α : Type u` and `P : α → Prop`, then a predicate has type `α → Prop`. Since `Prop` is impredicative, quantification over a type can still produce a proposition. In practice, a theorem can quantify over values in an arbitrarily high universe and remain a proposition:

```lean
universe u

def IsFixed {α : Type u} (f : α → α) : Prop :=
  ∀ x, f x = x
```

The universe of the carrier `α` does not force the proposition itself into a data universe. This distinction is why `Prop` is not simply another spelling for `Type 0`.

## 4. Read the universe of function and product types

If `α : Sort u` and `β : Sort v`, a nondependent function type `α → β` inhabits `Sort (max u v)`, with the special impredicative behavior when the result is a proposition. This is the source of many `max` expressions in elaborated signatures. You usually do not need to write those expressions yourself; you need to recognize what they say.

For example, a function can take a type as its input:

```lean
universe u

def listOfTypes : List (Type u) := []
```

Here the elements of the list are themselves types in `Type u`. The list therefore lives in a universe large enough to contain those type-valued elements. The type universe grows one level when a type is itself used as a value. The same `+ 1` relationship that defines `Type u = Sort (u + 1)` explains why `Type u` is an element of `Type (u + 1)`.

This is the basis for the familiar “type of types” error. Suppose a declaration expects a value `α : Type 0`, and you pass `Type` itself as that value. But `Type` is not a type in `Type 0`; it is a type in the next universe. Lean reports the mismatch because the API expects a small type, while the argument is itself the universe of small types.

Read such diagnostics literally. Identify the expected sort, the actual sort, and which parameter forced the expected universe. The error is often pointing to a real mismatch in the API rather than asking for a cast.

## 5. Universe levels in structures and dependent packages

A structure may contain fields at different universes. The structure's own universe must be high enough to contain those fields. For example, a package can associate a type of one level with data drawn from another:

```lean
universe u v

structure HasRepresentation (α : Type u) where
  Code : Type v
  encode : α → Code
```

The type parameter `α` and the field type `Code` are independently polymorphic. A `HasRepresentation α` can choose a representation type at a different level from its source. This is useful in generic interfaces whose representations may be richer than the mathematical objects represented.

Universe inference works by collecting constraints from fields, parameters, and results. When a universe error arises in a structure, inspect each field's sort. A field that stores `Type u` is storing a type as data, so its own sort is one level above the stored type. A field that merely stores an element of `α` does not introduce that extra level. This distinction is a common source of off-by-one errors in declarations involving type-valued fields.

The same analysis applies to bundles such as equivalences and algebraic homomorphisms. Their carriers contribute universe parameters; their proof fields live in `Prop` and generally do not raise the data level in the way another carrier type would. Reading the structure fields is often enough to understand why the resulting bundle has the universe it does.

## 6. Cumulativity and when `ULift` is appropriate

Lean's universe hierarchy is cumulative: a type at a lower universe can be used where a higher universe is expected, subject to universe constraints. This is convenient because generic APIs rarely need exact level equality. However, cumulative use does not erase the distinction between a type and the next universe containing that type.

`ULift` provides an explicit way to place a type in a higher universe while preserving its elements up to an equivalence. It is a legitimate tool when an API boundary imposes a universe arrangement that cannot be met directly. It is not a universal repair for every universe error.

Before inserting a lift, ask:

1. Did the API mean to accept a type in an arbitrary universe, or did it accidentally fix a universe?
2. Is the argument itself a type-valued object, adding a level that the author overlooked?
3. Can the parameter use a different universe variable, or can the type constructor be made universe-polymorphic?
4. Is the universe mismatch part of a genuine boundary between two libraries?

If the first three questions reveal an unnecessarily restrictive declaration, generalize that declaration. A lift changes the type the proof manipulates and may introduce coercions or transport obligations. That cost is worthwhile only when the universe boundary is real.

## 7. A practical diagnosis procedure

When a universe error appears, reduce the problem to a small type-level question rather than editing the entire theorem at once.

**Step 1: Read the complete expected and actual types.** Do not focus only on the `Type 1` phrase. Note the expression in which the mismatch occurs and which implicit arguments Lean inferred.

**Step 2: Inspect the signature of the involved declaration.** Use `#check` on the function, structure, or theorem. The printed universe parameters often reveal that a declaration was fixed to one level or that a type parameter appears where a value parameter was intended.

**Step 3: Write the level intent explicitly on a scratch declaration.** For example, distinguish `{α : Type u}` from `{α : Sort u}`. If two parameters should vary independently, use distinct variables such as `u` and `v` rather than accidentally sharing a level.

**Step 4: Generalize the API, not every call site.** If the declaration is meant to be generic, give it universe-polymorphic parameters. Lean can then infer a suitable instantiation at each use.

**Step 5: Add a lift only after identifying a real boundary.** If two external structures intentionally use incompatible levels, an explicit equivalence or lift can document the boundary. Keep that conversion at the interface rather than threading it through unrelated proofs.

This process is analogous to diagnosing a type mismatch, except the differing objects are the levels that classify types. In both cases, adding coercions before understanding the intended types can hide an API defect.

## 8. Universe-polymorphic API design

Good library declarations are general enough to be reused, but not more general than their meaning. The following guidelines help find that balance.

- Let Lean infer universe parameters for ordinary generic functions unless explicit declarations improve clarity.
- Use `Type u` for computational carriers and containers; use `Sort u` when propositions and data genuinely share the API.
- Use separate universe variables for independently varying inputs. Reuse a single variable only when the relationship is mathematically intended.
- Avoid fixing a carrier to `Type` (universe zero) when the declaration should work at arbitrary universes.
- Avoid unnecessary type-valued fields. If a declaration stores types, account for the additional universe level they require.
- Keep `ULift` and related wrappers at explicit interface boundaries, with a named equivalence where clients need to move values back and forth.
- Inspect public signatures with `#check`. A proof may compile while the declaration silently quantifies over more parameters than the intended API needs.

There is a maintainability benefit to polymorphic declarations. A theorem stated for `{α : Type u}` will usually apply to a high-universe carrier without a copied theorem or a chain of transports. The theorem states the real abstraction boundary: it depends on the operations and assumptions supplied, not on the universe where the carrier happens to live.

At the same time, universe polymorphism should not become a contest in maximal generality. If a theorem uses natural number recursion, finite enumeration, or computational data, the relevant types often need to be in `Type`. A signature that quantifies over arbitrary `Sort` may invite impossible elimination or obscure the assumptions. The signature is part of the explanation of the theorem; choose the level range that makes the theorem both reusable and understandable.

## 9. Common failure modes

### A polymorphic definition works only at universe zero

Inspect whether its type parameter is written without a universe variable under an option or section that fixed it, or whether a local declaration accidentally specialized the parameter. Generalize to `Type u` when the API should cover higher universes.

### The universe grows by one unexpectedly

Check whether the declaration stores a type as a value. `Type u` itself lives at the next level, so a container of types must live higher than a container of ordinary values.

### `Sort u` creates an elimination error

The implementation may have assumed data elimination that is unavailable when the type is `Prop`. Decide whether proposition inputs truly belong in the API. If not, narrow the parameter to `Type u`.

### A universe mismatch is “fixed” with many lifts

Inspect the original declarations first. One monomorphic type constructor or an inadvertently shared level parameter can cause a cascade of lifts. Repairing the API can remove all of them.

### Two level variables unexpectedly become equal

Check whether the signature reused a single variable for independent parameters. Give them separate universes when their values may range independently; preserve a shared universe only when that relation is part of the interface.

## 10. Exercises

1. Use `#check` on `id`, `List`, `Prod`, and `Equiv`. Identify each visible universe parameter and describe what determines the universe of its result.
2. Define a generic wrapper for values at universe `u`, then state an extraction function. Explain why the wrapper should not be specialized to `Type`.
3. Write one identity-like function over `Type u` and another over `Sort u`. Give an example of a proposition accepted by the latter and explain why that extra generality is useful.
4. Define a function from `α : Type u` to `β : Type v` and inspect its signature. Which universe expressions are inferred, and why?
5. Design a structure with a carrier type and a representation type at independent levels. Use `#check` to inspect the resulting declaration.
6. Find a universe mismatch in a small example involving `Type` as a value. Explain the expected sort and actual sort before correcting the declaration.
7. Take an API that inserts `ULift` to make a function typecheck. Determine whether the underlying declarations can be made universe-polymorphic instead. If the lift is necessary, state the boundary it represents.

## Summary

`Prop` is `Sort 0`, and `Type u` is `Sort (u + 1)`. Universe polymorphism lets one declaration work at many levels, just as type polymorphism lets it work at many types. Use `Type u` for data and `Sort u` only when propositions belong in the API. Read `max`, `imax`, and successor levels as constraints on what a declaration contains. Diagnose universe errors from the involved signatures, generalize an unnecessarily fixed API, and reserve `ULift` for genuine universe boundaries.

## Further reading

- [Lean reference: Universes](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/)
- [Lean reference: Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)
- [Theorem Proving in Lean 4: Types as Objects](https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#types-as-objects)
