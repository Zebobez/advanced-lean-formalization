# Chapter 3 — State the Algebra You Need

> **Audience.** This chapter assumes that you can read implicit arguments and use common algebraic operations in Lean. It develops the next step: stating the weakest algebraic assumptions that support a proof, then letting typeclass inference provide the concrete operations.

Many mathematical theorems are not about one particular type. The same argument may work for natural numbers, lists under append, matrices, or an abstract algebraic object. Lean's structures and typeclasses let a theorem name the laws it needs once and then apply wherever those laws are available.

This is more than a convenience for overloaded notation. A theorem with the right assumptions is a reusable interface: the proof records which algebraic laws matter, while typeclass inference supplies the corresponding operations and laws for each concrete type.

## Learning objectives

By the end of the chapter, you should be able to:

- read a theorem's typeclass assumptions as part of its mathematical claim;
- recognize the difference between an ordinary implicit parameter and an instance-implicit parameter;
- prove a theorem over an abstract structure and instantiate it at a concrete type;
- avoid assuming commutativity or other laws that the proof does not use;
- diagnose common typeclass synthesis failures without treating them as proof failures.

## 1. From one example to a general theorem

The following identity is familiar for multiplication:

\\[
a^{m+n} = a^m a^n.
\\]

One could prove it separately for natural-number multiplication, matrix multiplication, and repeated list append. But the proof uses the same facts in each setting: there is an associative operation, an identity element, and powers generated from that operation. Those laws are exactly what a monoid packages.

Lean can state the theorem once for an arbitrary monoid. We will prove it directly by induction on the second exponent. A standard algebra library already contains results of this form; this proof is included to show how the abstraction makes the argument reusable.

> **Theorem 3.1 (addition of exponents).** Let `M` be a monoid, and let `a : M`. For all natural numbers `m` and `n`, raising `a` to `m + n` is the same as multiplying its `m`th and `n`th powers.

In symbols, the claim is \\(a^{m+n} = a^m a^n\\). The order of the factors is part of the statement: the theorem is intended to hold even when multiplication is not commutative.

```lean
universe u

namespace Chapter03

variable {M : Type u} [Monoid M]

theorem power_add_induction (a : M) (m n : Nat) :
    a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        a ^ (m + (n + 1)) = a ^ (m + n) * a := by
          rw [Nat.add_succ, pow_succ]
        _ = (a ^ m * a ^ n) * a := by
          rw [ih]
        _ = a ^ m * (a ^ n * a) := by
          rw [mul_assoc]
        _ = a ^ m * a ^ (n + 1) := by
          rw [pow_succ]

end Chapter03
```

The proof never uses commutativity. It uses the recursive law for natural-number addition, the recursive law for powers, and associativity of multiplication. That observation is the key to selecting the assumption `[Monoid M]` rather than a stronger structure such as a commutative monoid.

The base case uses the unit laws. When `n = 0`, the left side reduces to `a ^ m`, while the right side is `a ^ m * 1`; simplification uses the identity element to close the equality. In the step case, the exponent on the left becomes one larger, so `pow_succ` moves one copy of `a` to the right. The induction hypothesis replaces the remaining power, and associativity changes only the grouping.

The inductive step can be read as five local transformations:

1. Nat.add_succ rewrites the exponent: \\(m + (n + 1) = (m + n) + 1\\).
2. pow_succ exposes one more factor: \\(a^{(m+n)+1} = a^{m+n} a\\).
3. The induction hypothesis replaces the remaining power: \\(a^{m+n} = a^m a^n\\).
4. mul_assoc changes the grouping: \\((a^m a^n)a = a^m(a^n a)\\).
5. pow_succ recognizes the final factor as a power: \\(a^n a = a^{n+1}\\).

Each line has a specific Lean counterpart. `Nat.add_succ` and `pow_succ` expose the recursive equations; the induction hypothesis replaces `a ^ (m + n)`; `mul_assoc` changes the grouping; and the last `pow_succ` restores a power on the right.

## 2. Read the assumptions as part of the API

The theorem's type is not just its conclusion. The bracketed assumption `[Monoid M]` says the proof requires an instance of the `Monoid` class for the type `M`.

```lean
#check @Chapter03.power_add_induction
```

The printed type shows that `{M : Type u}` is an ordinary implicit argument: Lean can often infer it from the type of `a`. The instance argument `[Monoid M]` is also implicit, but Lean treats it specially. It asks typeclass synthesis to find a structure that supplies the operations and laws required by `Monoid`.

Square brackets in a binder are a deliberate signal to the reader. Compare the two conceptual inputs to the theorem:

```text
{M : Type u}      the carrier type, inferred from the explicit argument a
[Monoid M]        the algebraic structure, synthesized from available instances
(a : M)           the element supplied by the caller
```

Ordinary implicit parameters are inferred from the surrounding term and expected type. Instance-implicit parameters are resolved from a database of candidate instances, including instances that may themselves require other instances. That recursive assembly is why a simple call such as `a ^ (m + n)` can select all the appropriate operations from the type of `a`.

The type `M` is the carrier; the class packages operations and proofs of their laws for that carrier. For this theorem, the relevant notation is `*` for multiplication and `^` for natural powers. The proof can use `mul_assoc` and `pow_succ` because those facts are available from the monoid instance and the library's algebraic API.

The picture is a flow from a concrete structure to a generic theorem:

```text
Nat with multiplication      Lists with append      Square matrices over a semiring
          │                         │                       │
          └────────── each has a Monoid instance ──────────┘
                                    │
                                    ▼
                       one theorem over [Monoid M]
```

The theorem does not inspect which concrete type it receives. It only uses the operations and laws promised by the interface.

## 3. Let inference supply the structure

Once the theorem is declared, using it at natural numbers does not require manually constructing a multiplication operation or proving associativity again:

```lean
example (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  exact Chapter03.power_add_induction a m n
```

Lean infers `M := Nat` from the type of `a`, then finds the standard monoid instance for `Nat`. The same theorem can be applied to other types with suitable instances. The notation is selected from the inferred type, so `*` and `^` now refer to the operations for that type.

You can ask Lean to display an instance it can synthesize:

```lean
#synth Monoid Nat
```

Or inspect the fully explicit form of the theorem:

```lean
#check @Chapter03.power_add_induction
```

The `@` disables ordinary implicit-argument insertion for this display, making the hidden parameters visible. The exact printed universe names are not important. Look for an argument that supplies `Monoid M`; that is the dictionary of operations and laws passed to the generic proof.

Typeclass synthesis is not a search for a proof of the theorem's conclusion. It is a type-directed search for the requested structure instance. The theorem's mathematical proof still has to be supplied. Keeping those two jobs separate helps diagnose errors: an unsolved goal is a proof problem, while “failed to synthesize instance” means Lean could not find the algebraic interface required by the declaration.

## 4. Choose the weakest useful structure

The proof above is valid in every monoid, including noncommutative monoids. If we had written `[CommMonoid M]`, the theorem would still be true, but its interface would unnecessarily exclude useful types. A noncommutative matrix monoid would not be accepted even though the proof never swaps factors.

This is a general design principle for formalization:

1. List the operations the proof uses.
2. List the laws required at each step.
3. Select the smallest existing structure that supplies those facts.
4. Revisit the choice if the proof later starts using an additional law.

The structure hierarchy is a library's vocabulary for common packages of operations and laws. Lean allows classes to build on other classes, so stronger assumptions can provide weaker interfaces automatically. When reading a theorem, focus first on the assumptions visible in its binders; those tell you the theorem's actual range of reuse.

The same principle applies to non-algebraic assumptions. Do not add `[DecidableEq α]` if the proof only needs a function `α → α → Bool`; do not assume finiteness if a local argument uses only an order relation; do not require a field if a semiring suffices. Each extra assumption narrows the callers that can use the theorem.

There is a practical balance here. A theorem stated for an extremely weak interface can be harder to prove and harder for users to discover if its assumptions do not correspond to a recognizable mathematical structure. Prefer the smallest standard class that clearly captures the required laws. If a library has a dedicated structure for the exact assumptions, use it; if not, a theorem with explicit hypotheses can be more transparent than inventing a new class for one result.

## 5. Typeclass errors and how to read them

### The type is not known yet

Typeclass inference can only select an instance when it knows the type parameters that determine it. If a variable's type is still a metavariable, Lean may report that the synthesis problem is stuck. Add the missing type annotation or make the relevant implicit argument explicit so the target class becomes concrete.

### The expected structure is absent

If a custom type does not have a `Monoid` instance, a theorem requiring `[Monoid M]` cannot be used for that type. This is not a request for a tactic to prove associativity at the call site. Either define the appropriate instance once, use a weaker theorem, or prove the result directly from the available operations.

### Several structures are available

Some mathematical objects support more than one operation. For example, natural numbers have both addition and multiplication, and each can be made into a monoid with its own identity. Libraries commonly use wrapper types to distinguish these structures. The wrapper changes the type-level interface while preserving the underlying values.

When a theorem is ambiguous or an operation has the wrong meaning, inspect the type Lean inferred for the expression. Use type ascriptions, named arguments, or the intended wrapper type to tell Lean which algebraic structure the proof is about. Do not rely on the visual symbol alone: `*` is notation whose meaning comes from the expected type.

Natural numbers illustrate the issue. Addition and multiplication both use the same carrier, but their identity elements differ: zero is the additive identity and one is the multiplicative identity. A bare statement such as “`Nat` is a monoid” uses the multiplication-based monoid. Libraries often provide wrapper types such as `Additive Nat` and `Multiplicative Nat` so that the same underlying values can carry distinct canonical structures without making the meaning of `+`, `*`, or `1` ambiguous.

The wrapper is not a runtime conversion that changes the number. It is a type-level choice that tells Lean which operation and laws a theorem should use. When notation gives a surprising result, follow the inferred type first; often the issue is that the proof is using the wrong algebraic viewpoint.

### Local instances should stay local

An instance declaration affects future typeclass synthesis in its scope. A local instance is useful when a structure is needed only for one section or proof. A global instance is appropriate when there is one canonical structure for the type and operation. Avoid registering competing global instances for the same class and type; callers should not need to guess which interpretation of the operation a theorem will use.

When debugging, `#synth` can show whether an instance is available. Lean's typeclass tracing options can reveal which candidates were considered, but first check the simpler questions: is the carrier type known, is the correct operation wrapper in use, and is the required instance in scope?

Do not add an instance merely to silence an error message. Before declaring one, identify the mathematical meaning of each operation and verify the laws it promises. A false instance can make later theorems appear to follow from an inconsistent interface. A duplicate but mathematically different instance can make notation depend on scope in a way that is difficult to maintain. If the alternative is local, keep the instance local and name the wrapper or operation that makes the choice explicit.

## 6. What abstraction buys—and what it does not

A theorem over `[Monoid M]` is reusable, but abstraction does not make every algebraic expression simplify automatically. It only gives the proof access to the facts in the structure and the lemmas built from them. If two expressions differ by a theorem that is not part of the active simplification interface, state or apply that theorem explicitly.

Nor should every short proof be generalized over a class. If a result is specifically about natural-number order, a theorem over `Nat` may be clearer and easier to use. Abstract only when the proof genuinely depends on a reusable collection of operations and laws.

Good abstraction has two parts: use the weakest useful assumption, and expose the operation in a way that callers can infer. A theorem with the right interface often needs no special call-site syntax at all. When it does, explicit type parameters and wrappers make the intended interpretation visible.

## 7. Exercises

1. Annotate every line of the proof of `power_add_induction` with the exact fact it uses. Which step would fail if multiplication were not associative?
2. The statement is valid for a noncommutative monoid. Give an example of a proof change that would require commutativity, then name the stronger structure you would need.
3. Instantiate the theorem at a type whose operation you know is associative, such as list append. Explain what the identity element and powers mean in that interpretation.
4. Inspect a theorem in Mathlib that has one or more bracketed assumptions. Write its type with `#check`, then identify which hidden structures its proof needs and which arguments Lean can infer from the goal.
5. A custom type has an associative operation but no identity element. Which assumptions in the monoid interface are stronger than necessary for a theorem that only reassociates the operation? State the weaker structure you would look for.

## Summary

Typeclasses let Lean express mathematical generality without manually threading operations and laws through every theorem call. Treat the bracketed assumptions as part of the theorem's API, choose the weakest structure the proof uses, and remember that instance synthesis supplies structure data rather than proving the theorem itself.

## Further reading

- The Lean 4 guide's chapter on [type classes](https://lean-lang.org/theorem_proving_in_lean4/Type-Classes/) explains instance-implicit arguments and automatic instance synthesis.
- The [Lean Language Reference on type classes](https://lean-lang.org/doc/reference/latest/Type-Classes/) gives the detailed syntax and behavior of class and instance declarations.
