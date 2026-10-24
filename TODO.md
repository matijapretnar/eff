# Old threads of development for consideration

In October 2026, unfinished branches, stashes and a local `todo.txt` were
deleted. Their code was small or did not compile, and its base was old, so it
is easier to write it again than to rebase it. Only the ideas and the
non-obvious decisions are kept here. Each section names its source, so that the
age of the idea is visible.

## Type inference

### Resolve constraints as soon as inference produces them

Sources: branch `incremental-unification` (4 June 2024), a stash on top of it
(14 June 2024), and `todo.txt` ("step 2: `infer_expression` does constraint
simplification; step 3: simplification by continuous unification").

Purpose: instead of collecting constraints and resolving them later, resolve
each constraint when inference produces it, so that typing information is
available locally. The queues in `UnresolvedConstraints` are then replaced by
the call stack.

Currently, `infer_expression` and `infer_computation` already call
`Unification.unify` after each subterm, but within one term, constraints still
go into the queues first.

1. Replace the step functions in `Unification` (`skel_eq_step`, `ty_eq_step`,
   `dirt_eq_step`, `dirt_omega_step`, `ty_omega_step`), which push
   sub-constraints back onto the queues, with mutually recursive functions
   `add_skeleton_equality`, `add_type_equality`, `add_dirt_equality`,
   `add_dirt_inequality` and `add_type_inequality`. Each of them first applies
   the current substitution to its arguments and then processes the
   sub-constraints by calling itself.
   - An inequality needs a coercion for each of its sub-inequalities: the
     coercion for `A₁ → C₁ ≤ A₂ → C₂` is built from the coercions for
     `A₂ ≤ A₁` and `C₁ ≤ C₂`. The stash kept coercion parameters: its
     `fresh_ty_coer` creates a fresh parameter `ω` and then calls
     `add_type_inequality ω ty1 ty2` at once, which later substitutes `ω`. A
     simpler alternative is to return the coercion directly, for example
     `add_type_inequality ty1 ty2 cnstrs : coercion * cnstrs`. Then only atomic
     constraints `α ≤ β` and `δ₁ ≤ O ∪ δ₂`, which go into the constraint graph,
     need coercion parameters.
   - The queues give an order: `unify` resolves the skeleton equality
     `ty1.ty = ty2.ty` before it splits the inequality `ty1 ≤ ty2`. Without the
     queues, `add_type_inequality` must call `add_skeleton_equality` itself
     before it splits the inequality.
2. Make `Infer` and `ConstraintSimplifier` call these functions instead of
   `UnresolvedConstraints.add_*` and `fresh_*_coer`.
3. Remove the queues, the `unify` loop and the calls to `unify` after each
   subterm. `UnresolvedConstraints.t` then reduces to `Constraints.t`.

The stash did most of steps 1 and 3 and part of step 2, but it did not compile.
It stopped at `apply_substitution`, which it left as `failwith __LOC__`. This is
the main open problem. When a new substitution changes a constraint that is
already in the constraint graph (for example, it substitutes `α` in `α ≤ β`),
the old `UnresolvedConstraints.apply_substitution` removed that constraint from
the graph and put it back onto a queue. Without queues, it must call
`add_*_inequality` again for each changed constraint, and these calls can add
further substitutions.

### Dirt inequalities with the same row

Source: stash on master (10 November 2025), made while fixing #89.

In `dirt_omega_step`, solve `ω : O₁ ∪ X ≤ O₂ ∪ X`, where both sides have the
same row `X`, directly when `O₁ ⊆ O₂`. This generalises the existing case
`O₁ ≤ O₂`, where `X = Ø`. Without it, the general case `O₁ ∪ δ₁ ≤ O₂ ∪ δ₂` with
`δ₁ = δ₂ = δ` refreshes `δ` to `δ'`, substitutes `δ ↦ δ'`, and adds the loop
edge `δ' ≤ O₂ ∪ δ'` to the constraint graph, which `Constraints.remove_loops`
later removes.

The stash had a bug: it reported an error whenever `O₁ ⊄ O₂`, also when `X` is a
parameter `δ`. Then the inequality is solvable by `δ ⊇ O₁ \ O₂`, so the new case
must have the guard `O₁ ⊆ O₂`. Because of this, the case does not make
`δ₁ ≠ δ₂` always true in the general case, and `todo.txt` asked about exactly
that: "`Substitution.apply_sub_dirtcoer sub_d` can be removed if always
`d1 != d2`".

### Track parameter polarities together with unresolved constraints

Source: branch `free-params-in-unresolved` (4 June 2024).

Purpose: during constraint simplification, keep the polarities of parameters
correct after each contraction, so that later contractions can depend on them.

`ConstraintSimplifier` computes the polarities of free parameters again with
`get_params` at each step. Instead, carry them through the simplification as a
pair `(params, unresolved)`:

- When an edge `p1 <= p2` is contracted (by adding the equality `p1 = p2`), also
  combine the polarities of `p1` and `p2` in `params`. This needs an
  `is_positive` function in `Type.FreeParams`.
- Use the tracked polarities to contract bridges one at a time. A bridge is a
  parameter that is not positive and has exactly one outgoing edge; for dirt
  parameters, that edge must also have no additional effects. Contract only one
  candidate per step, because contracting it can change the polarity of the
  other candidates.

### Check exhaustiveness on typed patterns

Source: stash on master, "Typed exhaustiveness" (2 June 2022).

`Exhaust` checks untyped patterns (`UntypedSyntax`). The stash changed it to
check typed patterns (`Term`): each constructor in the check carries its type
(`type cons = { cons : cons'; ty : Type.ty }`), so the missing patterns that
the check builds are typed terms. This needed the smart constructors
`Term.pConst` and `Term.pNonbinding`. The stash did not change `Infer`, which
still calls the check with untyped patterns. The purpose was not recorded.

### Index skeleton arguments by skeleton parameters

Sources: branch `fix-skeleton-apply` (25 April 2024, rebased onto
`coercion-simplifications` in May 2024), and probably the note
"`Skeleton.Apply`" in `todo.txt`.

`Skeleton.Apply` stores the skeletons of its arguments by the type parameters
of the type definition (`skel_args : t TyParam.Map.t`), so the skeleton layer
depends on the type layer, and `Type.apply` computes the skeleton from the type
arguments. The branch stored them by the skeleton parameters of the definition
instead (`skel_args : t Skeleton.Param.Map.t`):

- `Skeleton` no longer refers to type parameters.
- `Type.Apply` and `TyCoercion.ApplyCoercion` get an explicit field for the
  skeleton arguments, and `Type.apply` takes it as an argument. The skeleton
  substitution in `apply_sub_ty'` and `apply_sub_tycoer` applies to this field.
- Unification of two applications of the same type asserts that their skeleton
  arguments are equal.
- The new form also allows a definition in which several type parameters share
  a skeleton parameter. Currently, `syntax_to_core_params` in the desugarer
  gives each type parameter its own fresh skeleton parameter.

The purpose was not recorded. The branch did not compile and stopped at:

- `fresh_ty_with_skel` for `Skeleton.Apply`, which it left as
  `failwith __LOC__`. A fresh type argument for the type parameter `p` must get
  the skeleton that the definition gives to `p`, with the skeleton parameters of
  the definition replaced by `skel_args`. The old code took the skeleton
  directly from `skel_args`.
- The callers of `Type.apply` in the desugarer and in `TypeDefinitionContext`,
  which must now compute the skeleton arguments, for example from the
  skeletons of the type arguments.
- The patterns on `Apply` and `ApplyCoercion` in the backends.

### Structural records

Source: branch `structural-records` (16 October 2019), on the code from before
explicit effects.

Make record types structural: `{ f₁ : τ₁; …; fₙ : τₙ }` is a type expression
that can occur anywhere, not only in a type definition. Nominal records are
recovered through a sum type with a single variant, `type t = T of { … }`.

The branch moved `TyRecord` from type definitions to type expressions, added a
record type, and typed a record expression or pattern as the record of the
types of its fields. Field labels then no longer belong to a type definition,
so `find_field` and the errors about unbound or shadowed field labels went
away. Two record types unified when they had the same fields with unifiable
types. Because there was no subtyping, a record pattern had to list all fields.
The branch stopped before the backends: the multicore backend had no case for
the record type, and OCaml has no structural records, so a backend must
generate nominal record types or use another representation.

Today, this needs a record skeleton, a record type, a record coercion (similar
to `TupleCoercion`), and cases in unification, substitution and both backends.
Since the type system now has coercions, width subtyping on records (a record
with more fields is a subtype of one with fewer) is an open design question;
it could also allow record patterns that list only some fields.

## Optimiser

### Optimise handlers with `finally`

Source: branch `optimize-handler-with-finally` (6 January 2022).

Purpose: let the optimiser reduce handlers with a `finally` clause, as it does
for plain handlers.

`reduce_computation'` in `src/04-optimizer/optimizer.ml` reduces
`handle c with h` only when `h` is a plain `Handler`. Add the case for
`HandlerWithFinally`: reduce `handle c with (h finally f)` to

```ocaml
bind_computation state
  (reduce_computation state (Term.handle (Term.handler handler_clauses, comp)))
  finally_clause
```

Then move the code shared with the plain `Handler` case into a separate
function.

### Handler values and nested handlers

Source: stash on master (6 May 2025).

- In `beta_reduce`, substitute handler values (`Term.Handler _`) even when the
  abstraction is not inlinable, as is already done for variables and constants.
  Handler reductions apply only when the handler is a literal `Handler`, so a
  handler bound by `let` prevents them.
- In `handle_computation`, add a case for a nested handler,
  `handle (handle c with h') with h`. The stash did not write the body.

### Smaller optimiser ideas

Source: `todo.txt`.

- Remove the operation clauses of a handler for operations that are not in the
  dirt of the handled computation.
- When specialising handlers, do not add a clause that forwards the other
  operations. (The original note was "handler specialization
  (`_ -> assert false`)".)
- Decide how many specialisations of a function are needed. Each dirt parameter
  can be either pure or impure. For example, Eff's `map` is both `map` and the
  monadic `mapM`. With `n` dirt parameters, this gives `2ⁿ` specialisations,
  but perhaps only the negative dirt parameters determine them.
- Disable the optimisations one by one to see whether any of them is redundant.
  Probably none is, because most of them are now syntax-oriented. This was
  done in 2021 on the code of that time; see "Configurable optimisations".

### Simplify coercions built from reflexive coercions

Source: `todo.txt` (for tuples; applications are the same by analogy).

`TyCoercion.tupleCoercion` and `TyCoercion.applyCoercion` build a
`TupleCoercion` or an `ApplyCoercion` even when all their components are
`ReflTy`. They should return `ReflTy` instead. The optimiser already removes a
cast whose coercion has equal source and target types, so this matters for such
a coercion inside a larger coercion.

### Remove `original_ty`

Source: `todo.txt`, a question for a meeting.

A variable occurrence `Term.Var` stores `original_ty`, the type of the variable
before instantiation, together with the `instantiation`. Its only use is in the
plain OCaml backend (`elab_expression'` in `translateExEff2NoEff.ml`). There, a
polymorphic function is compiled once, for impure dirt parameters. When an
occurrence instantiates some dirt parameters to the empty dirt, the backend
casts the variable from the impure to the pure representation, and it uses
`original_ty` to find where these dirt parameters occur.

If functions are specialised for pure and impure dirt parameters (see
"Smaller optimiser ideas"), this cast and `original_ty` are no longer needed.
Otherwise, the backend could look up the type scheme of the variable instead of
storing its type in each occurrence.

### Curried specialisations

Source: branch `partial-optimizations` on jO-Osko's fork, commit `01b4eb3c`
(10 August 2021).

When the optimiser specialises a function for a handler whose value clause
varies, the specialised function takes the argument and the continuation built
from the value clause as a tuple, so its type is `(A × (B → C!Δ)) → C!Δ`. The
commit changed it to take them one after the other, with the type
`A → ((B → C!Δ) → C!Δ)`, where the second arrow is pure. It added
`handle_specialized_abstraction` to build the body.

### Configurable optimisations

Source: branch `partial-optimizations` (August 2021, mostly by Filip). Our copy
ended at `697b2e33`; jO-Osko's fork has 5 more commits, up to `d306a536`.

The command-line option `--optimizations <bitmask>` turns individual
optimisations on and off. The branch used it to generate the benchmarks
`queens`, `range`, `tree`, `loop`, `interp` and `capability_benchmarks` with
each optimisation disabled in turn (`NoFunSpec`, `NoCoerElim`, `NoCoerPush`,
`NoHandReduc`, `NoPureTrans`).

It also fixed two bugs that are still on master and on
`coercion-simplifications`:

1. `src/eff/eff.ml` reads the bitmask wrongly. It gives the five flags the
   numbers 0–4 and enables a flag `k` when `Int.logor bitmask k = 1`. So
   `push_coercions`, `handler_reductions` and `purity_aware_translation` are
   always disabled, `specialize_functions` is enabled only for the bitmask 1,
   and `eliminate_coercions` only for the bitmasks 0 and 1. The fix is to use
   the numbers `Int.shift_left 1 k` and to enable a flag when
   `Int.logand bitmask k <> 0`. The bug matters only when `--optimizations` is
   given; otherwise, the defaults in `Config` apply.
2. The flag `purity_aware_translation` has no effect. `translateExEff2NoEff.ml`
   and `translateNoEff2Ocaml.ml` receive it in their configuration but never
   read it. The fix (commits `697b2e33` and `41412ab0`) is to treat a dirt as
   empty in the translation only when the flag is enabled, through a function
   `is_empty_dirt state drt`, and to leave out casts when it is disabled. Also,
   `OcamlPrimitives.primitive_source` takes the flag, so that
   `translateNoEff2Ocaml.ml` prints the pure or the impure version of each
   primitive.

## Module structure

Source: branch `clean-up-language` (January 2022).

- Make `Variable` its own module (`Symbol.Make (Symbol.String)`) instead of a
  submodule of `Term`.
- Move `UntypedSyntax` from `01-language` to `02-parser`, so that the language
  library contains only the typed core language. The typechecker then depends
  on the parser library.
- Move typed patterns from `Term` to a new module `Pattern`: the type
  `Pattern.t`, the smart constructors (including `pConst` and `pNonbinding`),
  `bound_vars` (renamed from `pattern_vars`) and `print`. This fits "Check
  exhaustiveness on typed patterns", which needed the same smart constructors.

## Examples

From `todo.txt`:

- Why does Eff not have one-sided coercions? Extract the example.
- There is no example for `with … handle do … in …`. The equation to show is

  ```eff
  with h handle
    do x <- c1 in
    c2
  ```

  is the same as `with h' handle c1`, where
  `h' = { h except ret x -> with h handle c2 }`.
