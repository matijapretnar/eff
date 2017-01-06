module EnvMap = Map.Make(Untyped.Variable)

type t = Value.value EnvMap.t

let empty = EnvMap.empty

let update x = EnvMap.add x

let lookup x env =
  try
    Some (EnvMap.find x env)
  with
  | Not_found -> None      
