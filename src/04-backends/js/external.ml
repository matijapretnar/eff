open Utils

let comparison_functions =
  Assoc.of_list [ ("===", "x => y => x === y"); ("<", "x => y => x < y") ]

let constants =
  Assoc.of_list
    [ ("infinity", "Infinity"); ("neg_infinity", "-Infinity"); ("nan", "NaN") ]

let arithmetic_operations =
  Assoc.of_list
    [
      ("~-", "x => -x");
      ("+", "x => y => x + y");
      ("-", "x => y => x - y");
      ("*", "x => y => x * y");
      ("/", "x => y => x / y");
      ("%", "x => y => x % y");
      ("**", "x => y => x ** y");
      ("exp", "Math.exp");
      ("expm1", "Math.expm1");
      ("log", "Math.log");
      ("log1p", "Math.log1p");
      ("cos", "Math.cos");
      ("sin", "Math.sin");
      ("tan", "Math.tan");
      ("acos", "Math.acos");
      ("asin", "Math.asin");
      ("atan", "Math.atan");
      ("sqrt", "Math.sqrt");
    ]

let string_operations = Assoc.of_list [ ("string_length", "a => a.length") ]

let conversion_functions =
  Assoc.of_list
    [
      ("to_string", "String");
      ("float_of_int", "x => x");
      ("int_of_float", "x => ~~x");
    ]

let other = Assoc.of_list [ ("throw", "function (x) { throw x; }") ]

let values =
  comparison_functions |> Assoc.concat constants
  |> Assoc.concat arithmetic_operations
  |> Assoc.concat string_operations
  |> Assoc.concat conversion_functions
  |> Assoc.concat other
