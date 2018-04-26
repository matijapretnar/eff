

type ('state,'letter) automaton = {
  initial    : 'state;
  final      : 'state;
  transition : ('state * 'letter * 'state list) list;
  transition_drt : ('state * 'letter * 'state list) list;
  currentState : 'state;
  prevtransition : ('state * 'letter * 'state list) list;
}

type alphabet =
  | Prim of (Type.prim_ty * bool)
  | Function of bool
  | Handler of bool
  | Alpha of (Params.ty_param * bool)
  | Domain of bool
  | Range of bool
  | Op of (OldUtils.effect * bool)
  | DirtVar of (Params.dirt_param * bool)

type statetype = int

type automatype = (statetype, alphabet) automaton

(** [fresh wrapper] creates a function that creates fresh instances and wraps
    them with the [wrapper] function *)
let fresh wrapper =
  let counter = ref (1) in
  fun () ->
    incr counter;
    assert (!counter >= 0);
    wrapper !counter
    

let get_new_state = fresh OldUtils.id

let empty = {
  initial = 0;
  final = 1;
  transition = [];
  transition_drt = [];
  prevtransition = [];
  currentState = 0;
}

(* add a transition to the finite state machine *)
let rec add_state_transition from f fin = function
  | [] -> (from, f, [fin]) :: []
  | (from2, f2, sts) :: lst when from == from2 && f == f2 -> (from, f, fin :: sts) :: lst
  | elem :: lst -> elem :: add_state_transition from f fin lst 

let get_current_state automat = automat.currentState

let set_current_state state automat = {automat with currentState = state}

(* add a transition to the final (accepting) state *)
let add_final_transition f automat = {automat with 
  prevtransition = automat.transition ; 
  transition = add_state_transition automat.currentState f automat.final automat.transition
}

(* add a transition to the final (accepting) state *)
let add_final_transition_drt f automat = {automat with
  transition_drt = add_state_transition automat.currentState f automat.final automat.transition_drt
}

let add_new_transition f automat = 
  let newState = get_new_state () in
  {
    automat with 
    prevtransition = automat.transition ; 
    transition = add_state_transition automat.currentState f newState automat.transition;
    currentState = newState
  }

let undo_last_change automat = {automat with transition = automat.prevtransition }

(* let toDFA =  *)

(* let simplify = *)

(********************)
(* PRINT OPERATIONS *)
(********************)

let boolToPolarity b = if (b) then "⁺" else "⁻"

let printAlphabet ?max_level enc ppf = 
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match enc with
  | Prim (p, b) -> 
    print ~at_level:1 "%s" ((Type.prim_to_string p) ^ (boolToPolarity b))
  | Function b -> 
    print ~at_level:1 "%s" ("->" ^ (boolToPolarity b))
  | Handler b -> 
    print ~at_level:1 "%s" ("=>" ^ (boolToPolarity b))
  | Alpha (a, b) -> 
    Params.print_ty_param a ppf
  | Domain b ->
    print ~at_level:1 "%s" ("d" ^ (boolToPolarity b))
  | Range b -> 
    print ~at_level:1 "%s" ("r" ^ (boolToPolarity b))
  | Op (eff, b) ->
    let print_operation op ppf =
      Print.print ppf "%s" op
    in
    print_operation eff ppf
  | DirtVar (a, b) ->
    Print.print ppf "%t" (Params.print_dirt_param a)

let printAuto automat = 
  let rec print_list = function 
    [] -> ()
    | e::l -> Format.fprintf Format.std_formatter "%i" e ; Format.fprintf Format.std_formatter " " ; print_list l in
  let print_transition (a, b, c) = 
    Format.fprintf Format.std_formatter "%i -(" a; 
    printAlphabet b Format.std_formatter; 
    Format.fprintf Format.std_formatter ")-> ["; 
    print_list c; 
    Format.fprintf Format.std_formatter "]\n"; 
    () in
  Format.fprintf Format.std_formatter "initial %d\n" automat.initial;
  Format.fprintf Format.std_formatter "final %d\n" automat.final;
  Format.fprintf Format.std_formatter "transitions\n";
  List.iter print_transition automat.transition;
  Format.fprintf Format.std_formatter "transitions drt\n";
  List.iter print_transition automat.transition_drt;
  Format.fprintf Format.std_formatter "end\n\n";
  ()

