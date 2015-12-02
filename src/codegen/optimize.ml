open Typed

let rec optimize_comp c =
  match c.term with
  | Bind (c1, c2) ->
    begin match c1.term with
    (*Bind x (Value e) c -> LetC x e c*)
    | Value e -> let_in ~loc:c.location e (optimize_comp c2)
    | _ -> c
    end
  | Handle (e1,c1) ->
    begin c1.term with

    (*Handle h (LetC x e c) -> LetC (x e) (Handle c h)*)
    | LetIn (e2,c2) -> let_in ~loc:c.location e2 (handle ~loc:c.location e1 c2)
    
    (*Handle (Handler vc ocs) (Value v) -> Apply (Lambda vc) v *)
    | Value v -> begin match e1.term with
    
                 (*Handle (Handler vc ocs) (Value v) -> Apply (Lambda vc) v *)
                 | Handler h -> apply ~loc:c.location (lambda ~loc:c.location h.value) v
                 | _-> c
    | _ -> c
  | _ -> c


let rec optimize_expr e =
  match e.term with
  | Lambda (p,c) -> 
    begin match c.term with 
    | Value v -> pure_lambda ~loc:e.location (p,v)
    | _ -> e

  | _ -> e