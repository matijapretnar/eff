type 'a located = {it: 'a; at: Location.t}

val fold : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val fold_map :
  ('state -> 'a -> 'state * 'b) -> 'state -> 'a list -> 'state * 'b list
