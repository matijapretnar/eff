open Typed

let rec optimize_comp c =
  match c.term with
  | Bind (c1, c2) ->
    begin match (optimize_comp c1).term with
    (*Bind x (Value e) c -> LetC x e c*)
    | Value e -> let_in ~loc:c.location e (optimize_abstraction c2)
    (*Bind x (Bind y c1 c2) c3 -> Bind y c1 (Bind x c2 c3)*)
(*    | Bind (c3,(p1,c4)) -> bind ~loc:c.location (bind ~loc:c.location  (optimize_comp c2) (optimize_comp (p,c3)) )
                                (optimize_comp (p1,c4)) *)
    | _ -> c
    end
  | Handle (e1,c1) ->
    begin match (optimize_comp c1).term with

    (*Handle h (LetC x e c) -> LetC (x e) (Handle c h)*)
    | LetIn (e2,a) -> let (p,c2) = a.term in 
                      let_in ~loc:c.location e2 (abstraction ~loc:c.location p (handle ~loc:c.location e1 c2))
    
    | Value v -> begin match e1.term with
    
                 (*Handle (Handler vc ocs) (Value v) -> Apply (Lambda vc) v *)
                 | Handler h -> apply ~loc:c.location (lambda ~loc:c.location h.value) v
                 | _-> c
                 end
    | _ -> c
    end
  | Apply (e1,e2) ->
     begin match (optimize_expr e1).term with
     (*Apply (PureLambda a) e -> Value (PureApply (PureLambda a) e)*)
     | PureLambda pure_abs -> let (p,e) = pure_abs.term in 
                                 value ~loc:c.location 
                                 (pure_apply ~loc:c.location 
                                             (pure_lambda ~loc:c.location pure_abs)
                                             (optimize_expr e2) ) 
     | _ -> apply ~loc:c.location (optimize_expr e1) (optimize_expr e2)
     end
  | _ -> c

and optimize_abstraction abs = let (p,c) = abs.term in abstraction ~loc:abs.location p (optimize_comp c) 

and  optimize_expr e =
  match e.term with
  | Lambda a -> 
    let (p,c) = a.term in
    begin match c.term with 
    (*Lambda (x, Value e) -> PureLambda (x, e)*)
    | Value v -> pure_lambda ~loc:e.location (pure_abstraction ~loc:e.location p v)
    | _ -> e
    end
  | _ -> e