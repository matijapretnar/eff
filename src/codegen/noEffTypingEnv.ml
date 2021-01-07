(* Utils for NoEff type inference *)

(* Global state *)

type state = {
  gblCtxt : typingEnv;
  effects : (NoEff.n_type * NoEff.n_type) Typed.EffectMap.t;
}

(* Local environment *)

type environment = {
  var_types : (NoEff.variable, NoEff.n_type) Assoc.t;
  ty_params : CoreTypes.TyParam.t list;
  ty_coer_types : (CoreTypes.TyCoercionParam.t, NoEff.n_type) Assoc.t;
}

let extend_ty_params st ty_var = { st with ty_params = ty_var :: st.ty_params }

let extend_var_types st t_var tty =
  { st with var_types = Assoc.update t_var tty st.var_types }

let addExternal st x ty = extend_var_types st x ty

let extend_ty_coer_types st tcp ctty =
  { st with ty_coer_types = Assoc.update tcp ctty st.ty_coer_types }

let initial_state =
  { var_types = Assoc.empty; ty_params = []; ty_coer_types = Assoc.empty }

(* Typing env (global context) *)

type typingEnv = (NoEff.variable, NoEff.n_type) Assoc.t

let empty = Assoc.empty

let lookup ctx x = Assoc.lookup x ctx

let update ctx x sch = Assoc.update x sch ctx

let return_context ctx = Assoc.to_list ctx

(* STIEN: De substitution nog aanpassen, gaat hier niet werken*)
let apply_sub ctx sub =
  Assoc.kmap
    (fun (var, ty) -> (var, Substitution.apply_substitutions_to_type sub ty))
    ctx
