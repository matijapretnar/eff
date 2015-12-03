open Typed

let rec optimize_comp c =
  match c.term with
  | Bind (c1, (p,c2)) ->
    begin match (optimize_comp c1).term with
    (*Bind x (Value e) c -> LetC x e c*)
    | Value e -> let_in ~loc:c.location e (optimize_comp (p,c2))
    (*Bind x (Bind y c1 c2) c3 -> Bind y c1 (Bind x c2 c3)*)
    | Bind (c3,(p1,c4)) -> bind ~loc:c.location (bind ~loc:c.location  (optimize_comp c2) (optimize_comp (p,c3)) )
                                (optimize_comp (p1,c4))
    | _ -> c
    end
  | Handle (e1,c1) ->
    begin match (optimize_comp c1).term with

    (*Handle h (LetC x e c) -> LetC (x e) (Handle c h)*)
    | LetIn (e2,c2) -> let_in ~loc:c.location e2 (handle ~loc:c.location e1 c2)
    
    | Value v -> begin match (optimize_expr e1).term with
    
                 (*Handle (Handler vc ocs) (Value v) -> Apply (Lambda vc) v *)
                 | Handler h -> apply ~loc:c.location (lambda ~loc:c.location h.value) v
                 | _-> c
                 end
    | _ -> c
    end
  | Apply (e1,e2) ->
     begin match (optimize_expr e1).term with
     (*Apply (PureLambda a) e -> Value (PureApply (PureLambda a) e)*)
     | PureLambda (p,e) -> value ~loc:c.location 
                                 (pure_apply ~loc:c.location 
                                             (pure_lambda ~loc:c.location (p,e))
                                             (optimize_expr e2) ) 
     | _ -> c
     end
  | _ -> c


let rec optimize_expr e =
  match e.term with
  | Lambda (p,c) -> 
    begin match c.term with 
    (*Lambda (x, Value e) -> PureLambda (x, e)*)
    | Value v -> pure_lambda ~loc:e.location (p,v)
    | _ -> e
    end
  | _ -> e