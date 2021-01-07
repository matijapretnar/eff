module V = Value

type translation = Exists of string | Unknown

let comparison_functions =
  Assoc.of_list [ ("=", Exists "(=)"); ("<", Exists "(<)") ]

let constants =
  Assoc.of_list
    [
      ("infinity", Exists "infinity");
      ("neg_infinity", Exists "neg_infinity");
      ("nan", Exists "nan");
    ]

let arithmetic_operations =
  Assoc.of_list
    [
      ("~-", Exists "(~-)");
      ("+", Exists "(+)");
      ("-", Exists "(-)");
      ("*", Exists "( * )");
      ("/", Exists "(/)");
      ("mod", Exists "(mod)");
      ("**", Exists "( ** )");
      ("~-.", Exists "(~-.)");
      ("+.", Exists "(+.)");
      ("-.", Exists "(-.)");
      ("*.", Exists "( *. )");
      ("/.", Exists "(/.)");
      ("exp", Exists "exp");
      ("expm1", Exists "expm1");
      ("log", Exists "log");
      ("log1p", Exists "log1p");
      ("cos", Exists "cos");
      ("sin", Exists "sin");
      ("tan", Exists "tan");
      ("acos", Exists "acos");
      ("asin", Exists "asin");
      ("atan", Exists "atan");
      ("sqrt", Exists "sqrt");
    ]

let string_operations =
  Assoc.of_list
    [ ("^", Exists "(^)"); ("string_length", Exists "String.length") ]

let conversion_functions =
  Assoc.of_list
    [
      ("to_string", Unknown);
      ("string_of_float", Exists "string_of_float");
      ("string_of_int", Exists "string_of_int");
      ("float_of_int", Exists "float_of_int");
      ("int_of_float", Exists "int_of_float");
    ]

let top_handler =
  "(fun c ->" ^ "  match c () with\n"
  ^ "  | effect (Print s) k -> (print_string s; continue k ())\n"
  ^ "  | effect (RandomInt i) k -> continue k (Random.int i)\n"
  ^ "  | effect (RandomFloat f) k -> continue k (Random.float f)\n"
  ^ "  | effect (Read ()) k -> continue k (read_line ())\n" ^ "  | x -> x )\n"

let other =
  Assoc.of_list
    [
      ("failwith", Exists "failwith"); ("_ocaml_tophandler", Exists top_handler);
    ]

let values =
  comparison_functions |> Assoc.concat constants
  |> Assoc.concat arithmetic_operations
  |> Assoc.concat string_operations
  |> Assoc.concat conversion_functions
  |> Assoc.concat other
