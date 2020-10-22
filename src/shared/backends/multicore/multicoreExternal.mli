(** External values.

    Here, we define values that cannot be defined in Eff itself.
    We need to give them the correct MulticoreOcaml name.
    For instance [string_length] is replaced by [String.length].
*)

type translation = Exists of string | Unknown

val values : (string, translation) Assoc.t
(** [values] is an association list of external names and values. *)
