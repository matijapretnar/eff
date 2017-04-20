(*
=== GENERATED FROM interpSmall.eff ===
commit SHA: cdd58493d3c35dbe6ccae6de26e33c6d63c76753
=== BEGIN SOURCE ===

external ( + ) : int -> int -> int = "+"
external ( * ) : int -> int -> int = "*"
external ( - ) : int -> int -> int = "-"
external ( ~- ) : int -> int = "~-"
external ( / ) : int -> int -> int = "/"

(******************************************************************************)

type term =
    | Num of int
    | Add of term * term
    | Mul of term * term
    | Sub of term * term
    | Div of term * term

effect DivByZero : unit -> int

let rec interp = function
  | Num b -> b
  | Add (l, r) ->
    let x = interp l in
    let y = interp r in
    x + y
  | Mul (l, r) ->
    let x = interp l in
    let y = interp r in
    x * y
  | Sub (l, r) ->
    let x = interp l in
    let y = interp r in
    x - y
  | Div (l, r) ->
    let y = interp r in
    let x = interp l in
    begin match y with
    | 0 -> #DivByZero ()
    | _ -> x / y
    end

let arithmeticHandler = handler
    | #DivByZero () k ->  -1

(******************************************************************************)

let addCase =
    Add (
        Add (
            Add ((Num 20), (Num 2)),
            Mul ((Num 1), (Num 2))
        ),
        Sub (
            Add ((Num 2), (Num 2)),
            Div ((Num 1), (Num 0))
        )
    );;

let rec createCase n =
    begin match n with
    | 1 -> (Div (Num 100, Num 10))
    | _ -> Add (addCase, (createCase (n - 1)))
    end

let finalCase = createCase 200

let bigTest () =
  with arithmeticHandler handle interp (createCase 200)

=== END SOURCE ===
*)

type ('eff_arg,'eff_res) effect = ..
type 'a computation =
  | Value: 'a -> 'a computation
  | Call: ('eff_arg,'eff_res) effect* 'eff_arg* ('eff_res -> 'a computation)
  -> 'a computation
type ('eff_arg,'eff_res,'b) effect_clauses =
  ('eff_arg,'eff_res) effect -> 'eff_arg -> ('eff_res -> 'b) -> 'b
type ('a,'b) handler_clauses =
  {
  value_clause: 'a -> 'b ;
  effect_clauses: 'eff_arg 'eff_res . ('eff_arg,'eff_res,'b) effect_clauses }
let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff,arg,k) -> Call (eff, arg, ((fun y  -> (k y) >> f)))
let rec handler (h : ('a,'b) handler_clauses) =
  (let rec handler =
     function
     | Value x -> h.value_clause x
     | Call (eff,arg,k) ->
         let clause = h.effect_clauses eff  in
         clause arg (fun y  -> handler (k y))
      in
   handler : 'a computation -> 'b)

let value (x : 'a) = (Value x : 'a computation)
let call (eff : ('a,'b) effect) (arg : 'a) (cont : 'b -> 'c computation) =
  (Call (eff, arg, cont) : 'c computation)
let rec lift (f : 'a -> 'b) =
  (function
   | Value x -> Value (f x)
   | Call (eff,arg,k) -> Call (eff, arg, ((fun y  -> lift f (k y)))) :
  'a computation -> 'b computation)
let effect eff arg = call eff arg value
let run =
  function | Value x -> x | Call (eff,_,_) -> failwith "Uncaught effect"
let ( ** ) =
  let rec pow a =
    let open Pervasives in
      function
      | 0 -> 1
      | 1 -> a
      | n ->
          let b = pow a (n / 2)  in
          (b * b) * (if (n mod 2) = 0 then 1 else a)
     in
  pow
let string_length _ = assert false
let to_string _ = assert false
let lift_unary f x = value (f x)
let lift_binary f x = value (fun y  -> value (f x y))
;;"End of pervasives"
let _var_1 = (+)
let _var_2 = ( * )
let _var_3 = (-)
let _var_4 = (~-)
let _var_5 = (/)
type term =
  | Num of int
  | Add of (term* term)
  | Mul of (term* term)
  | Sub of (term* term)
  | Div of (term* term)
type (_,_) effect +=
  | Effect_DivByZero: (unit,int) effect
let rec _interp_6 _gen_let_rec_function_7 =
  match _gen_let_rec_function_7 with
  | Num _b_8 -> value _b_8
  | Add (_l_9,_r_10) ->
      (_interp_6 _l_9) >>
        ((fun _x_11  ->
            (_interp_6 _r_10) >> (fun _y_12  -> value (_x_11 + _y_12))))
  | Mul (_l_14,_r_15) ->
      (_interp_6 _l_14) >>
        ((fun _x_16  ->
            (_interp_6 _r_15) >> (fun _y_17  -> value (_x_16 * _y_17))))
  | Sub (_l_19,_r_20) ->
      (_interp_6 _l_19) >>
        ((fun _x_21  ->
            (_interp_6 _r_20) >> (fun _y_22  -> value (_x_21 - _y_22))))
  | Div (_l_24,_r_25) ->
      (_interp_6 _r_25) >>
        ((fun _y_26  ->
            (_interp_6 _l_24) >>
              (fun _x_27  ->
                 match _y_26 with
                 | 0 ->
                     call Effect_DivByZero ()
                       (fun _result_2  -> value _result_2)
                 | _ -> value (_x_27 / _y_26))))

let _arithmeticHandler_29 comp =
  handler
    {
      value_clause = (fun _gen_id_par_40  -> value _gen_id_par_40);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_DivByZero  ->
               (fun (() : unit)  -> fun (_k_30 : int -> _)  -> value (- 1))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b -> _)
                                                                    ->
                                                                    _)
    } comp

let _addCase_31 =
  Add
    ((Add ((Add ((Num 20), (Num 2))), (Mul ((Num 1), (Num 2))))),
      (Sub ((Add ((Num 2), (Num 2))), (Div ((Num 1), (Num 10))))))

let rec _createCase_32 _n_33 =
  match _n_33 with
  | 1 -> Div ((Num 100), (Num 0))
  | _ -> Add (_addCase_31, (_createCase_32 (_n_33 - 1)))
let _finalCase_37 = _createCase_32 200
let _bigTest_38 () =
  let rec _interp_5 _gen_let_rec_function_7 =
    match _gen_let_rec_function_7 with
    | Num _b_8 -> (* ADDED *) value (* ADDED *) _b_8
    | Add (_l_9,_r_10) ->
        let rec _new_special_var_142 (_gen_let_rec_function_7,_k_val_141) =
          match _gen_let_rec_function_7 with
          | Num _b_8 -> _k_val_141 _b_8
          | Add (_l_9,_r_10) ->
              _new_special_var_142
                (_l_9,
                  (fun _lift_fun_329  ->
                     (* value *)
                       ((fun _x_158  ->
                           _new_special_var_142
                             (_r_10,
                               (fun _lift_fun_330  ->
                                  (* value *)
                                    ((fun _y_159  ->
                                        _k_val_141 (_x_158 + _y_159))
                                       _lift_fun_330)))) _lift_fun_329)))
          | Mul (_l_14,_r_15) ->
              _new_special_var_142
                (_l_14,
                  (fun _lift_fun_331  ->
                     (* value *)
                       ((fun _x_173  ->
                           _new_special_var_142
                             (_r_15,
                               (fun _lift_fun_332  ->
                                  (* value *)
                                    ((fun _y_174  ->
                                        _k_val_141 (_x_173 * _y_174))
                                       _lift_fun_332)))) _lift_fun_331)))
          | Sub (_l_19,_r_20) ->
              _new_special_var_142
                (_l_19,
                  (fun _lift_fun_333  ->
                     (* value *)
                       ((fun _x_188  ->
                           _new_special_var_142
                             (_r_20,
                               (fun _lift_fun_334  ->
                                  (* value *)
                                    ((fun _y_189  ->
                                        _k_val_141 (_x_188 - _y_189))
                                       _lift_fun_334)))) _lift_fun_333)))
          | Div (_l_24,_r_25) ->
              _new_special_var_142
                (_r_25,
                  (fun _lift_fun_335  ->
                     (* value *)
                       ((fun _y_215  ->
                           _new_special_var_142
                             (_l_24,
                               (fun _lift_fun_336  ->
                                  (* value *)
                                    ((fun _x_216  ->
                                        match _y_215 with
                                        | 0 -> (* ADDED *) value (* ADDED *)(- 1)
                                        | _ -> _k_val_141 (_x_216 / _y_215))
                                       _lift_fun_336)))) _lift_fun_335)))
           in
        _new_special_var_142
          (_l_9,
            (fun _x_118  ->
               let rec _new_special_var_119
                 (_gen_let_rec_function_121,_k_val_120) =
                 match _gen_let_rec_function_121 with
                 | Num _b_122 -> _k_val_120 _b_122
                 | Add (_l_124,_r_123) ->
                     _new_special_var_119
                       (_l_124,
                         (fun _lift_fun_337  ->
                            (* value *)
                              ((fun _x_125  ->
                                  _new_special_var_119
                                    (_r_123,
                                      (fun _lift_fun_338  ->
                                         (* value *)
                                           ((fun _y_126  ->
                                               _k_val_120 (_x_125 + _y_126))
                                              _lift_fun_338)))) _lift_fun_337)))
                 | Mul (_l_128,_r_127) ->
                     _new_special_var_119
                       (_l_128,
                         (fun _lift_fun_339  ->
                            (* value *)
                              ((fun _x_129  ->
                                  _new_special_var_119
                                    (_r_127,
                                      (fun _lift_fun_340  ->
                                         (* value *)
                                           ((fun _y_130  ->
                                               _k_val_120 (_x_129 * _y_130))
                                              _lift_fun_340)))) _lift_fun_339)))
                 | Sub (_l_132,_r_131) ->
                     _new_special_var_119
                       (_l_132,
                         (fun _lift_fun_341  ->
                            (* value *)
                              ((fun _x_133  ->
                                  _new_special_var_119
                                    (_r_131,
                                      (fun _lift_fun_342  ->
                                         (* value *)
                                           ((fun _y_134  ->
                                               _k_val_120 (_x_133 - _y_134))
                                              _lift_fun_342)))) _lift_fun_341)))
                 | Div (_l_136,_r_135) ->
                     _new_special_var_119
                       (_r_135,
                         (fun _lift_fun_343  ->
                            (* value *)
                              ((fun _y_137  ->
                                  _new_special_var_119
                                    (_l_136,
                                      (fun _lift_fun_344  ->
                                         (* value *)
                                           ((fun _x_138  ->
                                               match _y_137 with
                                               | 0 -> (* ADDED *) value (* ADDED *)(- 1)
                                               | _ ->
                                                   _k_val_120
                                                     (_x_138 / _y_137))
                                              _lift_fun_344)))) _lift_fun_343)))
                  in
               _new_special_var_119 (_r_10, (fun _y_139  -> (* ADDED *) value (* ADDED *) (_x_118 + _y_139)))))
    | Mul (_l_14,_r_15) ->
        ((fun comp  ->
            handler
              {
                value_clause =
                  (fun _x_295  ->
                     (* value *)
                       (let rec _new_special_var_296
                          (_gen_let_rec_function_298,_k_val_297) =
                          match _gen_let_rec_function_298 with
                          | Num _b_299 -> _k_val_297 _b_299
                          | Add (_l_301,_r_300) ->
                              _new_special_var_296
                                (_l_301,
                                  (fun _lift_fun_345  ->
                                     (* value *)
                                       ((fun _x_302  ->
                                           _new_special_var_296
                                             (_r_300,
                                               (fun _lift_fun_346  ->
                                                  (* value *)
                                                    ((fun _y_303  ->
                                                        _k_val_297
                                                          (_x_302 + _y_303))
                                                       _lift_fun_346))))
                                          _lift_fun_345)))
                          | Mul (_l_305,_r_304) ->
                              ((fun comp  ->
                                  handler
                                    {
                                      value_clause =
                                        (fun _x_306  ->
                                           (* value *)
                                             (_new_special_var_296
                                                (_r_304,
                                                  (fun _lift_fun_347  ->
                                                     (* value *)
                                                       ((fun _y_307  ->
                                                           _k_val_297
                                                             (_x_306 * _y_307))
                                                          _lift_fun_347)))));
                                      effect_clauses = fun (type a) -> fun
                                        (type b) ->
                                        fun (x : (a,b) effect)  ->
                                          (match x with
                                           | Effect_DivByZero  ->
                                               (fun (() : unit)  ->
                                                  fun (_k_308 : int -> _)  ->
                                                    value (- 1))
                                           | eff' ->
                                               (fun arg  ->
                                                  fun k  ->
                                                    Call (eff', arg, k)) :
                                          a -> (b -> _) -> _)
                                    } comp)) (_interp_6 _l_305)
                          | Sub (_l_310,_r_309) ->
                              ((fun comp  ->
                                  handler
                                    {
                                      value_clause =
                                        (fun _vcvar_314  ->
                                           (* value *) (_k_val_297 _vcvar_314));
                                      effect_clauses = fun (type a) -> fun
                                        (type b) ->
                                        fun (x : (a,b) effect)  ->
                                          (match x with
                                           | Effect_DivByZero  ->
                                               (fun (() : unit)  ->
                                                  fun (_k_315 : int -> _)  ->
                                                    value (- 1))
                                           | eff' ->
                                               (fun arg  ->
                                                  fun k  ->
                                                    Call (eff', arg, k)) :
                                          a -> (b -> _) -> _)
                                    } comp))
                                ((_interp_6 _l_310) >>
                                   (fun _x_311  ->
                                      (_interp_6 _r_309) >>
                                        (fun _y_312  ->
                                           value
                                             (let _gen_bind_313 =
                                                _var_3 _x_311  in
                                              _gen_bind_313 _y_312))))
                          | Div (_l_317,_r_316) ->
                              ((fun comp  ->
                                  handler
                                    {
                                      value_clause =
                                        (fun _vcvar_321  ->
                                           (* value *) (_k_val_297 _vcvar_321));
                                      effect_clauses = fun (type a) -> fun
                                        (type b) ->
                                        fun (x : (a,b) effect)  ->
                                          (match x with
                                           | Effect_DivByZero  ->
                                               (fun (() : unit)  ->
                                                  fun (_k_322 : int -> _)  ->
                                                    value (- 1))
                                           | eff' ->
                                               (fun arg  ->
                                                  fun k  ->
                                                    Call (eff', arg, k)) :
                                          a -> (b -> _) -> _)
                                    } comp))
                                ((_interp_6 _r_316) >>
                                   (fun _y_318  ->
                                      (_interp_6 _l_317) >>
                                        (fun _x_319  ->
                                           match _y_318 with
                                           | 0 ->
                                               (effect Effect_DivByZero) ()
                                           | _ ->
                                               value
                                                 (let _gen_bind_320 =
                                                    _var_5 _x_319  in
                                                  _gen_bind_320 _y_318))))
                           in
                        _new_special_var_296
                          (_r_15, (fun _y_323  -> (* ADDED *) value (* ADDED *)(_x_295 * _y_323)))));
                effect_clauses = fun (type a) -> fun (type b) ->
                  fun (x : (a,b) effect)  ->
                    (match x with
                     | Effect_DivByZero  ->
                         (fun (() : unit)  ->
                            fun (_k_324 : int -> _)  -> value (- 1))
                     | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) :
                    a -> (b -> _) -> _)
              } comp)) (_interp_6 _l_14)
    | Sub (_l_19,_r_20) ->
        ((fun comp  ->
            handler
              {
                value_clause =
                  (fun _gen_id_par_325  -> value _gen_id_par_325);
                effect_clauses = fun (type a) -> fun (type b) ->
                  fun (x : (a,b) effect)  ->
                    (match x with
                     | Effect_DivByZero  ->
                         (fun (() : unit)  ->
                            fun (_k_326 : int -> _)  -> value (- 1))
                     | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) :
                    a -> (b -> _) -> _)
              } comp))
          ((_interp_6 _l_19) >>
             (fun _x_21  ->
                (_interp_6 _r_20) >> (fun _y_22  -> value (_x_21 - _y_22))))
    | Div (_l_24,_r_25) ->
        ((fun comp  ->
            handler
              {
                value_clause =
                  (fun _gen_id_par_327  -> value _gen_id_par_327);
                effect_clauses = fun (type a) -> fun (type b) ->
                  fun (x : (a,b) effect)  ->
                    (match x with
                     | Effect_DivByZero  ->
                         (fun (() : unit)  ->
                            fun (_k_328 : int -> _)  -> value (- 1))
                     | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) :
                    a -> (b -> _) -> _)
              } comp))
          ((_interp_6 _r_25) >>
             (fun _y_26  ->
                (_interp_6 _l_24) >>
                  (fun _x_27  ->
                     match _y_26 with
                     | 0 ->
                         call Effect_DivByZero ()
                           (fun _result_7  -> value _result_7)
                     | _ -> value (_x_27 / _y_26))))
     in
  _interp_5 (_createCase_32 200)
