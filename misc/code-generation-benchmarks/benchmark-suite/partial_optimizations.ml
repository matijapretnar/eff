open OcamlHeader

let return x = Value x

let binary_fun f x = return (fun y -> return (f x y))

let plus = binary_fun ( + )

let minus = binary_fun ( - )

let equal = binary_fun ( = )

type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

type (_, _) eff_internal_effect += Incr : (unit, unit) eff_internal_effect

let get s = Call (Get, s, fun s -> Value s)

let put s = Call (Put, s, fun s -> Value s)

let fail s = Call (Fail, s, fun _y_52 -> Value _y_52)

let incr s = Call (Incr, s, fun _y_52 -> Value _y_52)

(* Generated and hand fixed coe for partially optimized versions *)

(* loop pure *)

let loop_pure__direct n =
  let rec loop n =
    equal n >>= fun f ->
    f 0 >>= fun b ->
    if b then return ()
    else
      minus n >>= fun h ->
      h 1 >>= fun n' -> loop n'
  in
  force_unsafe (loop n)

let loop_pure__purity_aware n =
  let rec loop n =
    let f = ( = ) n in
    let b = f 0 in
    if b then return ()
    else
      let h = ( - ) n in
      let n' = h 1 in
      loop n'
  in
  force_unsafe (loop n)

let loop_pure__opt n =
  let rec loop_pure_42 _x_48 =
    if _x_48 = 0 then () else loop_pure_42 (_x_48 - 1)
  in
  loop_pure_42 n

let loop_pure__native n =
  let rec loop_pure n' = if n' = 0 then () else loop_pure (n' - 1) in
  loop_pure n

(* loop latent *)

let less_than = binary_fun ( < )

let loop_latent__direct n =
  let rec loop n =
    equal n >>= fun f ->
    f 0 >>= fun b ->
    if b then return ()
    else
      less_than n >>= fun f ->
      f (-1) >>= fun b ->
      if b then fail () >>= fun x -> Value (match x with _ -> assert false)
      else
        minus n >>= fun h ->
        h 1 >>= fun n' -> loop n'
  in
  force_unsafe (loop n)

let loop_latent__purity_aware n =
  let rec loop n =
    let f = ( = ) n in
    let b = f 0 in
    if b then return ()
    else
      let f = ( < ) n in
      let b = f (-1) in
      if b then fail () >>= fun x -> Value (match x with _ -> assert false)
      else
        let h = ( - ) n in
        let n' = h 1 in
        loop n'
  in
  force_unsafe (loop n)

let loop_latent__opt n =
  let rec _loop_latent_56 _x_67 =
    if _x_67 = 0 then Value ()
    else if _x_67 < 0 then
      Call
        ( Fail,
          (),
          fun (_y_76 : empty) -> Value (match _y_76 with _ -> assert false) )
    else _loop_latent_56 (_x_67 - 1)
  in
  force_unsafe (_loop_latent_56 n)

exception FailE

let loop_latent__native n =
  let rec loop_latent n' =
    if n' = 0 then () else if n' < 0 then raise FailE else loop_latent (n' - 1)
  in
  loop_latent n

(* loop incr *)

let loop_incr__direct n =
  let _incr_handler_53 =
    handler
      {
        value_clause =
          (fun (_x_59 : unit) ->
            Value
              (let _y_60 = _x_59 in
               fun (_x_61 : int) -> _x_61));
        effect_clauses =
          (fun (type a b) (eff : (a, b) eff_internal_effect) :
               (a -> (b -> _) -> _) ->
            match eff with
            | Incr ->
                fun () _l_64 ->
                  Value
                    (fun (_x_55 : int) ->
                      let _b_56 =
                        coer_arrow coer_refl_ty force_unsafe _l_64 ()
                      in
                      let _b_57 =
                        let _b_58 = ( + ) _x_55 in
                        _b_58 1
                      in
                      _b_56 _b_57)
            | eff' -> fun arg k -> Call (eff', arg, k));
      }
  in
  let rec loop n =
    equal n >>= fun f ->
    f 0 >>= fun b ->
    if b then return ()
    else
      incr () >>= fun _ ->
      minus n >>= fun h ->
      h 1 >>= fun n' -> loop n'
  in
  force_unsafe (_incr_handler_53 (loop n)) 0

let loop_incr__purity_aware n =
  let _incr_handler_53 =
    handler
      {
        value_clause =
          (fun (_x_59 : unit) ->
            Value
              (let _y_60 = _x_59 in
               fun (_x_61 : int) -> _x_61));
        effect_clauses =
          (fun (type a b) (eff : (a, b) eff_internal_effect) :
               (a -> (b -> _) -> _) ->
            match eff with
            | Incr ->
                fun () _l_64 ->
                  Value
                    (fun (_x_55 : int) ->
                      let _b_56 =
                        coer_arrow coer_refl_ty force_unsafe _l_64 ()
                      in
                      let _b_57 =
                        let _b_58 = ( + ) _x_55 in
                        _b_58 1
                      in
                      _b_56 _b_57)
            | eff' -> fun arg k -> Call (eff', arg, k));
      }
  in
  let rec loop n =
    let f = ( = ) n in
    let b = f 0 in
    if b then return ()
    else
      incr () >>= fun _ ->
      let h = ( - ) n in
      let n' = h 1 in
      loop n'
  in
  force_unsafe (_incr_handler_53 (loop n)) 0

let loop_incr__opt n =
  let rec _loop_incr_114 _x_89 _x_0 =
    if _x_89 = 0 then _x_0 else _loop_incr_114 (_x_89 - 1) (_x_0 + 1)
  in
  _loop_incr_114 n 0

let loop_incr__native n =
  let rec loop_incr counter n' =
    if n' = 0 then counter else loop_incr (counter + 1) (n' - 1)
  in
  loop_incr 0 n

(* loop, we call this loop_state *)
let loop_state__direct n =
  let rec loop n =
    equal n >>= fun f ->
    f 0 >>= fun b ->
    if b then return ()
    else
      get () >>= fun s ->
      plus s >>= fun g ->
      g 1 >>= fun s' ->
      put s' >>= fun _ ->
      minus n >>= fun h ->
      h 1 >>= fun n' -> loop n'
  in
  let state_handler =
    handler
      {
        effect_clauses =
          (fun (type a b) (eff : (a, b) eff_internal_effect) :
               (a -> (b -> _) -> _) ->
            match eff with
            | Put ->
                fun (_s'_45 : int) _l_61 ->
                  Value
                    (fun (_ : int) ->
                      let _b_47 =
                        coer_arrow coer_refl_ty force_unsafe _l_61 ()
                      in
                      _b_47 _s'_45)
            | Get ->
                fun () _l_62 ->
                  Value
                    (fun (_s_49 : int) ->
                      let _b_50 =
                        coer_arrow coer_refl_ty force_unsafe _l_62 _s_49
                      in
                      _b_50 _s_49)
            | eff' -> fun arg k -> Call (eff', arg, k));
        value_clause = (fun _ -> return (fun s -> return s));
      }
  in
  force_unsafe (state_handler (loop n) >>= fun f -> f 0)

let loop_state__purity_aware n =
  let rec loop n =
    let f = ( = ) n in
    let b = f 0 in
    if b then return ()
    else
      get () >>= fun s ->
      let g = ( + ) s in
      let s' = g 1 in
      put s' >>= fun _ ->
      let h = ( - ) n in
      let n' = h 1 in
      loop n'
  in
  let state_handler =
    handler
      {
        effect_clauses =
          (fun (type a b) (eff : (a, b) eff_internal_effect) :
               (a -> (b -> _) -> _) ->
            match eff with
            | Put ->
                fun (_s'_45 : int) _l_61 ->
                  Value
                    (fun (_ : int) ->
                      let _b_47 =
                        coer_arrow coer_refl_ty force_unsafe _l_61 ()
                      in
                      _b_47 _s'_45)
            | Get ->
                fun () _l_62 ->
                  Value
                    (fun (_s_49 : int) ->
                      let _b_50 =
                        coer_arrow coer_refl_ty force_unsafe _l_62 _s_49
                      in
                      _b_50 _s_49)
            | eff' -> fun arg k -> Call (eff', arg, k));
        value_clause = (fun _ -> return (fun s -> return s));
      }
  in
  force_unsafe (state_handler (loop n) >>= fun f -> f 0)

let loop_state__native n =
  let rec loop_state n' state =
    if n' = 0 then state else loop_state (n' - 1) (state + 1)
  in
  loop_state n 0

and loop_state__opt n =
  let rec loop_state2 n' state =
    if n' = 0 then state else loop_state2 (n' - 1) (state + 1)
  in
  loop_state2 n 0
