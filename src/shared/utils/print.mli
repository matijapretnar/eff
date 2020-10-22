(** Pretty-printing functions *)

val error :
  ?loc:Location.t -> string -> ('a, Format.formatter, unit) format -> 'a
(** Print an error to the standard error channel. *)

val check : ?loc:Location.t -> ('a, Format.formatter, unit) format -> 'a
(** Print a check to the standard error channel. *)

val warning : ?loc:Location.t -> ('a, Format.formatter, unit) format -> 'a
(** Print a warning to the standard error channel. *)

val debug : ?loc:Location.t -> ('a, Format.formatter, unit) format -> 'a
(** Print a debug message to the standard error channel. *)

val print :
  ?at_level:int ->
  ?max_level:int ->
  Format.formatter ->
  ('a, Format.formatter, unit) format ->
  'a
(** Print a construct to a given formatter, possibly parenthesizing it.

    Each construct has a level [at_level] at which it is printed. The lower the
    level, the tighter the construct. Next, each construct is printed in some
    context, which determines the maximum allowed level [max_level] at which the
    construct can still be printed without putting it in parentheses.

    As an example, let us look at untyped lambda calculus, naively defined as
    {[
      type term =
        | Var of string
        | App of term * term
        | Abs of string * term
    ]}

    - Variables are atomic constructs so we print them at the lowest level.
    - Application is left associative, so we print [App (App (e1, e2), e3)]
      as ["e1 e2 e3"], but [App (e1, App (e2, e3))] as ["e1 (e2 e3)"].
      We achieve this by printing [App (e1, e2)] at level 1 and limiting the
      maximum level of [e1] to 1 and of [e2] to 0.
    - Lambda abstraction has the lowest precedence, so we print it at level 2.
      The abstraction binds everything that follows it, so the level of its body
      is unlimited.

    The most convenient way to express this is as follows.
    {[
      let rec print_term ?max_level e ppf =
        let print ?at_level = Print.print ?max_level ?at_level ppf in
        match e with
        | Var x -> print "%s" x
        | App (e1, e2) ->
          print ~at_level:1 "%t %t"
            (print_term ~max_level:1 e1) (print_term ~max_level:0 e2)
        | Abs (x, e) -> print ~at_level:2 "lam %s. %t" x (print_term e)
    ]}
    We define a recursive function [print_term ?max_level e ppf] that prints [e]
    at [max_level] to the pretty-printer [ppf]. Since each case will be printed
    with the same [max_level], we define a helper function [print], which we
    call to print each case with its specified [at_level]. We format the term
    using a format string where subterms are printed by placing ["%t"] and
    calling [print_term] with the appropriate [max_level]. For more details on
    format strings, take a look at the [Format] module in the standard OCaml
    library.

    Note that the default value of [at_level] is [min_int] to easily print
    atomic constructs or constructs with their own delimiters (variables,
    constants, lists, ...). Conversely, the default value of [max_level] is
    [max_int] to easily print parts that are already delimited by the construct,
    for example the guard in a conditional, which is delimited on both sides by
    [if] and [then], or a body of the quantifier, which is on one side delimited
    by [.] and on the other side unlimited. *)

val sequence :
  string ->
  ('a -> Format.formatter -> unit) ->
  'a list ->
  Format.formatter ->
  unit
(** [sequence sep pp lst ppf] uses pretty-printer [pp] to print elements of
    [lst] separated by [sep] to the formatter [ppf]. *)

val tuple :
  ('a -> Format.formatter -> unit) -> 'a list -> Format.formatter -> unit
(** [tuple pp lst ppf] prints a tuple given by a list of elements [lst] using
    a pretty-printer [pp] to the formatter [ppf]. *)

val record :
  ('f -> Format.formatter -> unit) ->
  ('v -> Format.formatter -> unit) ->
  ('f, 'v) Assoc.t ->
  Format.formatter ->
  unit
(** [record fpp vpp lst ppf] prints a record given by an associative list of elements
    [lst] using a pretty-printer [fpp] for fields and [vpp] for values to the formatter
    [ppf]. *)
