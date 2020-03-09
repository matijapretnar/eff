(* Type inference for NoEff *)

module NoEff = NoEffSyntax
module Util = NoEffTypingEnv

let rec coer_infer (state: Util.state) (env: Util.environment) (coer: NoEff.n_coercion) = 
  match coer with
  | NoEff.NCoerVar par ->
    ( match (Assoc.lookup par env.ty_coer_types) with
    | Some xtype -> (xtype, NoEff.NCoerVar par)
    | None -> failwith "Coercion variable out of scope" )
