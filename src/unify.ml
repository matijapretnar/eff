module C = Common
module T = Type

(* [unify tctx sbst pos t1 t2] solves the equation [t1 = t2] and stores the solution in
   the substitution [sbst]. *)
let unify tctx sbst pos t1 t2 =
  (* [transparent t] tells us whether the type constructor [t] is transparent, i.e.,
     do we unfold it during unificiation. *)
  let rec unify t1 t2 =
    let t1 = T.subst_ty !sbst t1 in
    let t2 = T.subst_ty !sbst t2 in
      match t1, t2 with

      | (t1, t2) when t1 = t2 -> ()

      (* The order of the next two clauses is important in case we have
         an equation between a [T.Meta] and a [T.Nonpoly] because we should
         not turn a T.Nonpoly to a T.Meta which might get polymorphic later on. *)
      | ((T.Param p, t) | (t, T.Param p)) ->
          if T.occurs_in_ty p t
          then begin
            let sbst = T.beautify2 t1 t2 in
            Error.typing ~pos:pos
              "This expression has a forbidden cylclic type %t = %t." (Print.ty ~sbst:sbst [] t1) (Print.ty ~sbst:sbst [] t2)
          end
          else
            let s = [(p, t)] in sbst := T.compose_subst s !sbst

      | (T.Arrow (u1, v1), T.Arrow (u2, v2)) ->
          unify v1 v2;
          unify u2 u1

      | (T.Tuple lst1, T.Tuple lst2) when List.length lst1 = List.length lst2 ->
          List.iter2 unify lst1 lst2

      | (T.Record lst1, T.Record lst2) ->
          assert false

      | (T.Sum lst1, T.Sum lst2) ->
          assert false

      | (T.Apply (t1, lst1), T.Apply (t2, lst2)) when t1 = t2 && List.length lst1 = List.length lst2  ->
          List.iter2 unify lst1 lst2
            (* The following two cases cannot be merged into one, as the whole matching
               fails if both types are Apply, but only the second one is transparent. *)

      | (T.Apply (t1, lst1), t2) when Tctx.transparent ~pos:pos tctx t1 ->
          unify t2 (Tctx.ty_apply ~pos:pos tctx t1 lst1)

      | (t2, T.Apply (t1, lst1)) when Tctx.transparent ~pos:pos tctx t1 ->
          unify t2 (Tctx.ty_apply ~pos:pos tctx t1 lst1)

      | (T.Handler h1, T.Handler h2) ->
          unify h2.T.value h1.T.value;
          unify h1.T.finally h2.T.finally

      | (T.Effect lst1, T.Effect lst2) ->
          assert false

      | (t1, t2) ->
          let sbst = T.beautify2 t1 t2 in
            Error.typing ~pos:pos
              "This expression has type %t but it should have type %t." (Print.ty ~sbst:sbst [] t1) (Print.ty ~sbst:sbst [] t2)
  in
    unify t1 t2
