(** External values.

    Here, we define values that cannot be defined in Eff itself. These include
    comparison functions, arithmetic and string operations, type conversion
    functions, standard input and output channel, a function for generating
    exceptions with pretty error messages, and random number generator.

    One can then bind an external value associated to a string [external_name]
    to an identifier [id] of type [ty] with the command
    [external id : ty = "external_name"].
*)

val values : (string, Backend.Value.value) Utils.Assoc.t
(** [values] is an association list of external names and values. *)
