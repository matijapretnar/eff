open CoreUtils
module V = Value

type translation = Exists of string | Unknown

let comparison_functions = Assoc.of_list [("=", "="); ("<", "<")]

let constants =
  Assoc.of_list
    [ ("infinity", Exists "infinity")
    ; ("neg_infinity", Exists "neg_infinity")
    ; ("nan", Exists "nan") ]

let arithmetic_operations =
  Assoc.of_list
    [ ("~-", Exists "~-")
    ; ("+", Exists "+")
    ; ("-", Exists "-")
    ; ("*", Exists "*")
    ; ("/", Exists "/")
    ; ("mod", Exists "mod")
    ; ("**", Exists "**")
    ; ("~-.", Exists "~-.")
    ; ("+.", Exists "+.")
    ; ("-.", Exists "-.")
    ; ("*.", Exists "*.")
    ; ("/.", Exists "/.")
    ; ("exp", Exists "exp")
    ; ("expm1", Exists "expm1")
    ; ("log", Exists "log")
    ; ("log1p", Exists "log1p")
    ; ("cos", Exists "cos")
    ; ("sin", Exists "sin")
    ; ("tan", Exists "tan")
    ; ("acos", Exists "acos")
    ; ("asin", Exists "asin")
    ; ("atan", Exists "atan")
    ; ("sqrt", Exists "sqrt")
    ]

let string_operations =
  Assoc.of_list [("^", Exsists "^"); ("string_length", Exsists "String.length")]

let conversion_functions =
  Assoc.of_list
    [ ("to_string", Unknown)
    ; ("float_of_int", Exists "float_of_int") ]
    ; ("float_of_int", Exists "float_of_int") ]
    ; ("float_of_int", Exists "float_of_int") ]    
    ; ("float_of_int", Exists "float_of_int") ]

let values =
  comparison_functions |> Assoc.concat constants
  |> Assoc.concat arithmetic_operations
  |> Assoc.concat string_operations
  |> Assoc.concat conversion_functions
