# Chapter 15 — Namespaces, Modules, and Typeclass Instances

> **Audience.** This chapter assumes you can write definitions and instances in Lean. It focuses on organizing a development so names, imports, and inferred structure remain predictable as the library grows.

A proof library is more than a collection of theorems. It is an interface that other files import and use. Namespaces decide how declarations are found; modules decide what files depend on each other; typeclass instances decide which structures Lean inserts automatically. These mechanisms make Lean libraries concise, but they can also create surprising behavior when their scope is unclear.

Good organization lets a reader answer three questions: where is this declaration defined, what must be imported to use it, and which instance did Lean infer? This chapter develops conventions and debugging tools for all three.

## Learning objectives

By the end of the chapter, you should be able to:

- organize declarations into namespaces that reflect the API;
- use sections and `variable` declarations without adding accidental arguments;
- distinguish namespaces from modules and control the import graph;
- use `open`, `open scoped`, and local scopes deliberately;
- define instances at the scope where they are canonical;
- inspect and debug typeclass synthesis with `#synth` and `infer_instance`.

## 1. Namespaces are API organization

A namespace groups declarations under a hierarchical name. It does not create a new type or isolate code at runtime. Its purpose is to organize the public API and keep common identifiers from colliding.

```lean
namespace FormalTools.Algebra

variable {M : Type _} [Monoid M]

def cube (x : M) : M := x * x * x

theorem cube_one : cube (1 : M) = 1 := by
  simp [cube]

end FormalTools.Algebra
```

Outside the namespace, the declarations are named `FormalTools.Algebra.cube` and `FormalTools.Algebra.cube_one`. This is useful even for a small project: a name tells the reader which part of the mathematical API owns it.

Names that appear in multiple domains should generally be placed in the namespace of the primary type or concept. Lean's generalized field notation then lets users write expressions such as `x.cube` when appropriate. The namespace should make discovery easier, not merely mirror file paths.

## 2. Sections and shared variables

Sections group commands that share local variables, options, notation, or instances. A `variable` declaration saves repetition when many theorems depend on the same type and structure:

```lean
namespace FormalTools.Algebra

section

variable {M : Type _} [Monoid M]

theorem cube_mul_one (x : M) : cube x * 1 = cube x := by
  simp [cube]

end
end FormalTools.Algebra
```

Variables used in a declaration become parameters of that declaration. Variables not used are omitted from its final signature. This is convenient, but it means the scope's variable declarations should be kept near the declarations that need them. Otherwise, a proof may inherit an unintended instance or trigger warnings about unused variables.

Use named section variables when the name clarifies a theorem's assumptions. Anonymous instance variables are concise when the instance is only needed for typeclass inference. If a section is long, split it into smaller sections so that variables and local settings do not remain active farther than necessary.

## 3. Namespaces and modules are different

A namespace organizes declaration names. A module is a source file that Lean elaborates and imports as a unit. A file can define declarations in several namespaces, and one namespace can be spread across multiple modules.

A useful project layout follows conceptual dependencies:

```text
Core definitions
       │
       ├── Basic lemmas
       │       ├── Algebraic interface
       │       └── Order interface
       └── Applications
```

Keep lower-level modules independent of higher-level applications. If a basic definition imports an application module just to reuse one theorem, move the shared theorem into an appropriate foundational module. This reduces import cycles and prevents a small declaration from bringing a large dependency graph into every client.

An import graph is a directed acyclic graph in a well-organized project: a module imports its prerequisites, and higher-level modules depend on it. A cycle usually means that two concepts have been placed at the same dependency level even though one is foundational to the other. Moving a small definition or interface theorem downward often resolves the cycle without duplicating code.

Lean requires imports at the start of a module. A declaration is available only if its defining module is imported directly or transitively. When a theorem seems to exist online but is unknown locally, check the module import and the version of the dependency before changing the theorem statement.

For a book example, `import Mathlib` is convenient and consistent. In a reusable library, narrower imports can improve compilation and make dependencies clearer. Reduce imports only when the project benefits from doing so; minimality is not worth making every file's dependency list obscure.

Large umbrella imports are convenient during exploration because they make declarations immediately available. As a library matures, import discipline matters for compile time, namespace visibility, and dependency review. Narrow imports help a reader see whether a theorem depends on topology, measure theory, or only elementary algebra. Do not shrink imports mechanically; first identify the actual dependency and whether a broader import is an intentional project convention.

## 4. Opening namespaces and scopes

An `open` command makes names from a namespace available without their prefixes in the current scope. It improves readability, but too many open namespaces can make an identifier ambiguous or hide where a theorem comes from.

Prefer a qualified name when the source matters or a name is easy to confuse. Use a local opening when several declarations from one namespace are used together. For a one-off name, `open Namespace in ...` limits the opening to a single command or expression.

`open scoped` has a narrower purpose: it activates scoped notation, scoped instances, or scoped attributes from a namespace without making all its ordinary declarations available. This is often appropriate for notation such as finite sums or algebraic syntax. It communicates that the file needs a notation scope rather than a broad namespace opening.

When parsing or instance synthesis changes unexpectedly, inspect the active scopes and `open` commands. A local notation or instance can make an expression elaborate differently from how its surface syntax suggests.

## 5. Typeclass instances are global search rules

An instance declaration tells Lean how to construct a typeclass value when one is requested. For example, `[Monoid M]` in a theorem signature is an implicit argument synthesized from the available instance environment. This lets a generic theorem use multiplication and identity without manually passing their implementation.

Instances should be coherent: for a given type and class, callers should normally see one canonical structure. A global instance that gives a type two competing monoid structures can make theorem statements ambiguous or cause instance search to select a surprising structure.

Before adding an instance, ask:

1. Is this structure canonical for the type?
2. Could a different module define another reasonable instance?
3. Should the instance be local or scoped instead of global?
4. Is a direct parameter more appropriate than automatic inference?

Use local instances for temporary proof choices and scoped instances when the choice should be activated only with a particular notation or scope. Avoid global “orphan” instances that connect a type and class owned by unrelated modules unless the structure is genuinely canonical and stable.

Typeclass inheritance is also part of the contract. A `CommMonoid` provides the monoid operations together with commutativity; generic theorems can request only the superclass they need. When defining a new class, make its required parent structures explicit and keep the class's laws focused on the additional behavior. This allows existing typeclass search to reuse inherited fields rather than requiring users to provide duplicate instances.

Do not encode every convenient theorem as an instance. Instances are intended to synthesize data or structure from type information. A theorem that one proposition implies another is usually a lemma, not a new instance rule. Adding theorem-like instances can make search take longer and can create surprising inference paths.

### Scope local choices as narrowly as possible

If an instance exists only to support one proof, place it in a local scope or introduce it with a local instance command. A section boundary then restores the previous environment. This is safer than registering a global instance that changes every later theorem in the file.

When two choices are mathematically meaningful, make the choice visible in the theorem statement. Passing an explicit structure value or using a wrapper type is more reliable than relying on the order in which competing instances are found. Priorities can resolve intentional overlap, but they should not be used to conceal an API that has no canonical default.

The same caution applies to notation classes and coercions. They affect how expressions are elaborated before type checking, so adding a new global notation or coercion can change how readers parse familiar syntax. Keep notation close to the concepts it represents, use scoped notation when the meaning is not universal, and prefer ordinary named functions when notation would hide the operation being performed.

## 6. Inspecting typeclass synthesis

The command `#synth` asks Lean to find an instance for a typeclass goal. The tactic `infer_instance` does the same inside a proof:

```lean
#synth Monoid Nat

example : Monoid Nat := by
  infer_instance
```

Use these tools when Lean reports that an instance is missing or when a theorem appears to use an unexpected structure. The expected type is the query: include all type parameters and constraints that should determine the instance.

If synthesis fails, check whether the needed import is present, whether a local instance has been introduced, and whether the requested class follows from the structures already available. If synthesis succeeds with an unintended instance, qualify the structure or use a local scope that selects the intended choice.

The result of `#synth` is a term, often a constructor applied to other instances. Reading that term can reveal which inheritance path Lean used. If the output is large, the relevant clue is usually the first typeclass argument whose concrete implementation differs from the one expected.

Instance priorities affect which candidates are considered first. They are an advanced tool for managing intentional overlaps, not a routine fix for ambiguous design. Prefer to remove the ambiguity at its source. A priority tweak can make one file elaborate while leaving downstream behavior difficult to predict.

## 7. Local structure choices

Sometimes one underlying type legitimately carries multiple structures. The natural numbers, for example, support several algebraic or order-related interfaces. A global instance is appropriate only when the library has a canonical choice that theorems should use by default.

When a proof needs a temporary alternative, introduce it locally or pass the relevant structure explicitly. This confines the choice and prevents it from changing unrelated theorem elaboration. If the mathematical objects should be distinguished permanently, model them with separate types or structures instead of relying on scope to distinguish their behavior.

This is especially important for notation. Two operations may both print as `+`, but mean different structures. A scoped notation or explicit namespace helps make the intended operation visible. If a proof changes when an `open` or `letI` command is moved, that is evidence the structure choice is part of the proof's meaning and should be made explicit.

## 8. Documentation and public declarations

Public definitions and theorems benefit from docstrings, stable names, and an intentional namespace. Internal implementation helpers can be placed in a `private` declaration or nested namespace if clients should not depend on them. Keep the public API focused on the statements that callers need.

Namespaces are not the same as visibility controls. A name inside `Internal` is still a name that can be imported and referenced if the module exposes it. If clients should not rely on a helper, mark it `private` or keep it in a file-local implementation layer. Conversely, a public theorem should not be made difficult to find merely because it appears in a file with a low-level name.

Documentation comments should explain what a public declaration means and when to use it. They do not need to repeat its type. For theorem families, a short namespace-level description or consistent naming pattern can be more useful than many nearly identical comments.

Use naming suffixes consistently when a family of declarations exposes equations, extensionality, or preservation laws. Consistency helps editor completion and source search reveal neighboring results. A reader should be able to guess where an application lemma belongs without memorizing an unrelated global name.

Attributes such as `[simp]`, `[ext]`, and `[instance]` alter how future declarations are elaborated or proved. Treat these as API decisions. A new global simp theorem can change simplification results in unrelated modules; a new instance can change typeclass synthesis. Prefer the smallest scope that achieves the intended behavior, and state the reason in a short comment when the effect is not obvious.

## 9. Common failure modes

### A declaration name collides with another API

Move it into the namespace of its concept or use a more descriptive name. Avoid broad `open` commands that make several unrelated short names available.

### A variable unexpectedly appears in a theorem signature

Check the active section variables and whether the declaration depends on them. Move unrelated variables into a smaller section.

### An import cycle develops

Move shared definitions or lemmas to a lower-level module that both clients can import. Keep applications above their prerequisites in the dependency graph.

### Typeclass search uses the wrong structure

Inspect active instances with `#synth`; scope or pass the intended structure explicitly. Avoid adding global instances solely to silence one error.

### A notation or instance appears without an obvious import

Check transitive imports and scoped openings. Namespace structure and module structure are independent, so the source file may differ from the declaration's namespace.

## 10. Exercises

1. Organize a small family of definitions and theorems under a namespace named for their main type.
2. Use section variables to share a typeclass assumption across two declarations. Inspect their final signatures with `#check`.
3. Move an unrelated variable into a smaller section and compare the declarations' signatures.
4. Use `#synth` to inspect a standard instance and explain which assumptions make it available.
5. Give an example where `open` makes a proof shorter but a fully qualified theorem name makes its meaning clearer.
6. Identify a global instance in Mathlib and explain why its choice is canonical. Contrast it with a structure that should be local or scoped.
7. Split a large source file into modules based on dependency direction. Draw the import graph and remove any unnecessary reverse dependency.

## Summary

Namespaces organize APIs; modules organize compiled source files and dependencies. Sections and `variable` declarations factor shared parameters but should be kept narrow. Use `open` and scoped notation deliberately. Typeclass instances are global synthesis rules, so introduce only canonical global choices and use local or scoped instances for temporary alternatives. Inspect failures with `#synth` and `infer_instance`, and treat attributes and instances as public API decisions.

## Further reading

- [Lean reference: Namespaces and Sections](https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/)
- [Lean reference: Type Classes](https://lean-lang.org/doc/reference/latest/Type-Classes/)
- [Lean reference: Instance Declarations](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/)
- [Lean reference: Source Files and Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)

