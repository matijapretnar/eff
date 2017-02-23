(********************************
* Types
********************************)

type term =
    | Num of int
    | Add of (term * term)
    | Mul of (term * term)
    | Sub of (term * term)
    | Div of (term * term)
    | Ref of term
    | Deref of term
    | Assign of (term * term)
    | Var of string
    | App of (termF * term)
and
  termF =
    | LambdaV of (string * term)
    | LambdaL of (string * term)
;;

(********************************
* Helper methods
********************************)

let absurd void = match void with | _ -> assert false;;

(* Helper methods for the state *)
let rec lookupState (x, y) =
    match y with
    | [] -> absurd ("VarNotFound")
    | (x', y) :: lst -> if x = x' then y else lookupState (x, lst);;

let updateState (k, v, env) =
    (k, v) :: env;;

let rec checkLoc (x, env) =
    begin match env with
    | [] -> false
    | (x', y) :: lst -> if x = x' then true else checkLoc (x, lst)
    end
;;

let rec createLoc (i, env) =
    if (checkLoc (i, env)) then
        createLoc ((i+1), env)
    else
        i
;;

let getNewLoc env = createLoc (0, env);;

(* Helper methods for the environment *)
let rec lookupEnv (x, y) =
    match y with
    | [] -> absurd ("VarNotFound")
    | (x', y) :: lst -> if x = x' then y else lookupState (x, lst);;

let extendEnv (k, v, env) =
    (k, v) :: env;;

(********************************
* Main interpreter method
********************************)


let rec interp a (env, s) =
    begin match a with
    | Num b -> (b, env, s)
    | Add (l, r) -> let (x, env2, s2) = (interp l (env, s)) in
                    let (y, env3, s3) = (interp r (env2, s2)) in
                    ((x + y), env3, s3)
    | Mul (l, r) -> let (x, env2, s2) = (interp l (env, s)) in
                    let (y, env3, s3) = (interp r (env2, s2)) in
                    ((x * y), env3, s3)
    | Sub (l, r) -> let (x, env2, s2) = (interp l (env, s)) in
                    let (y, env3, s3) = (interp r (env2, s2)) in
                    ((x - y), env3, s3)
    | Div (l, r) -> let (x, env2, s2) = (interp l (env, s)) in
                    let (y, env3, s3) = (interp r (env2, s2)) in
                    ((x / y), env3, s3)
    | Ref x ->
        let (x_interp, env2, s2) = interp x (env, s) in
        let x_loc = getNewLoc s2 in
        let s_updated = updateState (x_loc, x_interp, s2) in
        (x_loc, env2, s_updated)
    | Deref x ->
        let (x_interp, env2, s2) = interp x (env, s) in
        (lookupState (x_interp, s), env, s)
    | Assign (lhs, rhs) ->
        let (x_loc, env2, s2) = interp lhs (env, s) in
        let (x_interp, env3, s3) = interp rhs (env2, s2) in
        let s_updated = updateState (x_loc, x_interp, s3) in
        (x_interp, env3, s_updated)
    | Var v -> (lookupEnv (v, env), env, s)
    | App (e1, e2) ->
        let interpFunc =
             begin match e1 with
             | LambdaV (st, t) ->
                    let envi = env in
                    (fun v ->
                        let ext = (extendEnv (st, v, envi)) in
                        let (t_res, env2, s2) = interp t (ext, s) in
                        (t_res, ext, s2)
                    )

             (*| LambdaL (s, t) ->
                    let envi = env in
                    (fun v ->
                      let x_loc = #AllocLoc () in
                      let thunk = #UpdateLoc (x_loc, v); v in
                      let tmp = #UpdateLoc (x_loc, thunk) in
                      let ext = (extendEnv (s, (#LookupLoc x_loc), envi)) in
                      let ext_2 = #SetEnv ext in
                      let t_res = interp t in
                     #InEnv (ext_2, t_res)
                    )*)
             end
        in
        let e1_interp = (interpFunc) in
        let (e2_interp, env2, s2) = (interp e2 (env, s)) in
        e1_interp e2_interp
    end
;;

(********************************
* Big Test
********************************)

let lambdaCase =
    LambdaV (
        "a",
        Add (
        (Var "a"),
    Num 22)

    );;

let addCase =
    Add (
        Add (
            Add (
                (Num 20),
                (Num 2)
            ),
            Mul (
                (Num 1),
                (Num 2)
            )
        ),
        Sub (
            Add (
                (Num 2),
                (Num 2)
            ),
            Add (
                (Num 1),
                (Num 2)
            )
        )
    );;

let testCaseA = App (lambdaCase, App (lambdaCase, App (lambdaCase, App (lambdaCase, App (lambdaCase, App (lambdaCase, App (lambdaCase, addCase)))))));;

let testCaseB = App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, testCaseA)))))));;

let testCaseC = App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, testCaseB)))))));;

let testCaseD = App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, testCaseC)))))));;

let rec createCase n =
    begin match n with
    | 1 -> testCaseD
    | _ -> App( lambdaCase, (createCase (n-1)))
    end;;

let finalCase = createCase 200;;

let bigTest () = interp (finalCase) ([],[]);;
