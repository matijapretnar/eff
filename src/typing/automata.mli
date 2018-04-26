(********************)
(* TYPE DEFINITIONS *)
(********************)

type alphabet =
  | Prim of (Type.prim_ty * bool)
  | Function of bool
  | Handler of bool
  | Alpha of (Params.ty_param * bool)
  | Domain of bool
  | Range of bool
  | Op of (OldUtils.effect * bool)
  | DirtVar of (Params.dirt_param * bool)

(* the state representation *)
type statetype

(* the automaton (NFA) *)
type automatype

(*************************)
(* CONSTRAINT OPERATIONS *)
(*************************)

(* the empty automaton. *)
val empty : automatype

val get_current_state : automatype -> statetype

val set_current_state : statetype -> automatype -> automatype

(* add a new transition to the nfa *)
val add_final_transition : alphabet -> automatype -> automatype

(* add a new transition to the nfa *)
val add_final_transition_drt : alphabet -> automatype -> automatype

(* add a new transition to the nfa *)
val add_new_transition : alphabet -> automatype -> automatype

val undo_last_change : automatype -> automatype

val printAuto : automatype -> unit