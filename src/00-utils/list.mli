include module type of Stdlib.List

val fold : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val fold_map :
  ('state -> 'a -> 'state * 'b) -> 'state -> 'a list -> 'state * 'b list

val left_to_right_map : ('a -> 'b) -> 'a list -> 'b list
(** Custom definition of map to ensure the order of sideffects. *)

val unique_elements : 'a list -> 'a list
(** Returns a list of all unique elements of given list. *)

val no_duplicates : 'a list -> bool
(** Checks that the list doesn't contain duplicates. *)

val list_diff : 'a list -> 'a list -> 'a list
(** Returns elements of the first list that or not present in the second. *)

val concat_map : ('a -> 'b list) -> 'a list -> 'b list

val equal : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
(** [equal eq [a1; ...; an] [b1; ..; bm]] holds when
    the two input lists have the same length, and for each
    pair of elements [ai], [bi] at the same position we have
    [eq ai bi].
    Note: the [eq] function may be called even if the
    lists have different length. If you know your equality
    function is costly, you may want to check {!compare_lengths}
    first.
    Natively available in: 4.12.0
*)
