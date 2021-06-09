  $ for f in valid/*.eff
  > do
  >   echo "======================================================================"
  >   echo $f
  >   echo "----------------------------------------------------------------------"
  >   ../eff.exe $f
  > done
  ======================================================================
  valid/choice.eff
  ----------------------------------------------------------------------
  - : int = 10
  val choose_all : 'a => 'a list = <handler>
  - : int list = [10; 5; 20; 15]
  val choose_all2 : 'a => 'a list = <handler>
  - : int list list = [[10; 5]; [20; 15]]
  - : int list list = [[10; 20]; [5; 15]]
  - : int list list = [[10; 20]; [10; 15]; [5; 20]; [5; 15]]
  val choose_int : int -> int -> int = <fun>
  val sqrt : int -> int option = <fun>
  val pythagorean : int -> int -> int * int * int = <fun>
  val backtrack : 'a => 'a = <handler>
  val choose_all : 'a => 'a list = <handler>
  - : (int * int * int) list = [(5, 12, 13); (6, 8, 10); (8, 15, 17);
                                (9, 12, 15)]
  ======================================================================
  valid/lexer.eff
  ----------------------------------------------------------------------
  - : int = 10
  - : int = 20
  - : int = 30
  - : int = 40
  - : int = -1000000000
  - : int = 42
  - : int = -42
  - : int = 42
  - : int = 42
  - : int = 11259375
  - : int = 11259375
  - : int = 32072
  - : int = 32072
  - : float = 3.141592
  - : float = 4.141592
  - : float = -5.1592
  - : float = 6.1592
  - : float = -3.14
  ======================================================================
  valid/orelse_andalso.eff
  ----------------------------------------------------------------------
  - : bool = false
  - : bool = true
  - : bool = false
  - : bool = false
  - : bool = false
  - : bool = true
  - : bool = false
  - : bool = true
  - : bool = true
  - : bool = true
  ======================================================================
  valid/patterns.eff
  ----------------------------------------------------------------------
  - : int = 5
  - : int * int = (1, 2)
  Warning (file "valid/patterns.eff", line 3, char 5):
  This pattern-matching is not exhaustive.
  
                                      Here is an example of a value that is not matched:
    []
  - : int * int list = (1, [2; 3; 4])
  Warning (file "valid/patterns.eff", line 4, char 5):
  This pattern-matching is not exhaustive.
  
                                      Here is an example of a value that is not matched:
    []
  - : int list = [2; 3; 4]
  - : int = 10
  - : int * int cow = (10, Moo 10)
  - : int * int * int = (42, 42, 42)
  - : int * int * int * (int * int * int) = (1, 2, 3, (1, 2, 3))
  ======================================================================
  valid/polymorphism.eff
  ----------------------------------------------------------------------
  val a : int * string = (5, "foo")
  - : int * string = (5, "foo")
  val g : 'a -> 'b -> 'a = <fun>
  - : int * string = (4, "foo")
  val u : 'a list = []
  - : int list * string list = ([1], ["foo"])
  val v : 'a list list = [[]]
  - : 'a list list * int list list = ([[]; []], [[2]; []])
  - : 'a -> 'a = <fun>
  - : 'a -> 'a = <fun>
  val u : 'a -> 'b = <fun>
  - : 'a -> 'b = <fun>
  ======================================================================
  valid/semisemi.eff
  ----------------------------------------------------------------------
  val a : int = 5
  val b : int = 6
  val c : int = 7
  - : int = 4
  - : int = 11
  ======================================================================
  valid/state.eff
  ----------------------------------------------------------------------
  val state : 'a -> 'b => int -> 'b = <fun>
  val better_state : int -> 'a => 'a = <fun>
  val transaction : 'a => 'a = <handler>
  Check (file "valid/state.eff", line 25, char 28):
  20
  Check (file "valid/state.eff", line 28, char 30):
  30
  Check (file "valid/state.eff", line 34, char 49):
  20
  - : int = 0
  ======================================================================
  valid/test_equality.eff
  ----------------------------------------------------------------------
  - : bool = true
  - : bool = false
  - : bool = true
  - : bool = false
  - : bool = false
  - : bool = true
  - : string * bool * bool * bool = ("nested", true, false, true)
  val f : 'a -> 'a -> bool = <fun>
  ======================================================================
  valid/test_less_than.eff
  ----------------------------------------------------------------------
  - : bool = false
  - : bool = true
  - : bool = false
  - : bool = false
  - : bool = true
  - : bool = false
  - : bool = false
  - : string = "composite values"
  - : bool = true
  - : bool = false
  - : string = "records"
  - : bool = true
  - : bool = false
  - : bool = true
  - : bool = false
  - : bool = true
  - : bool = false
  ======================================================================
  valid/test_stdlib.eff
  ----------------------------------------------------------------------
  val less1 : bool = true
  val less2 : bool = false
  val less3 : bool = false
  val test_equal_int : bool = true
  val test_equal_float : bool = true
  - : unit = ()
  - : unit = ()
  - : unit = ()
  - : unit = ()
  val tilda_minus : int = -1
  val tilda_minus_dot2 : float = -3.14159
  val tilda_minus_dot2 : float = -1.
  val test_plus : int = 4
  val test_times : int = 4
  val test_power : int = 8
  val test_minus : int = 19
  val test_minus_tilda_minus : int = 65
  val test_mod1 : int = 2
  val test_mod2 : int = 0
  Check (file "valid/test_stdlib.eff", line 45, char 1):
  Call DivisionByZero ()
  - : unit = ()
  Check (file "valid/test_stdlib.eff", line 47, char 1):
  Call DivisionByZero ()
  - : unit = ()
  val test_plus_dot : float = 5.84
  val test_times_dot : float = 8.478
  val test_minus_dot : float = 0.44
  val test_div_dot : float = 1.16296296296
  val test_div_dot_zero : float = infinity
  val test_div : int = 33
  Check (file "valid/test_stdlib.eff", line 61, char 1):
  Call DivisionByZero ()
  - : unit = ()
  val test_zero_div : int = 0
  Check (file "valid/test_stdlib.eff", line 65, char 1):
  Call DivisionByZero ()
  - : unit = ()
  val test_carron : string = "cherrypie"
  val test_string_of_float1 : string = "12."
  val test_string_of_float2 : string = "12."
  val test_string_of_float3 : string = "-12.000009"
  val test_string_of_int1 : string = "0"
  val test_string_of_int2 : string = "-18"
  val test_to_string1 : string = "13"
  val test_to_string2 : string = "[(1, 2, 3)]"
  val test_to_string3 : string = "(1, 2, 3)"
  val test_to_string4 : string = "<fun>"
  val test_int_of_float1 : int = -1
  val test_int_of_float2 : int = 12
  val test_float_of_int : float = 42.
  val test_none : 'a option = None
  val test_some : int option = Some 3
  val test_ignore : unit = ()
  val test_not : bool = false
  val test_greater1 : bool = true
  val test_greater2 : bool = true
  val test_leq : bool = true
  val test_geq : bool = true
  val test_neq : bool = true
  val test_range : int list = [4; 5; 6; 7; 8; 9]
  val test_map : int list = [1; 4; 9; 16; 25]
  val test_take : int list = [2; 5; 8; 11; 14; 17; 20; 23; 26; 29; 32; 35; 38;
                              41; 44; 47; 50; 53; 56; 59; 62]
  val test_fold_left : int = 89
  val test_fold_right : int = 161
  Check (file "valid/test_stdlib.eff", line 121, char 27):
  "iter [1; 2; 3; 4; 5]"
  val test_iter : unit = ()
  val test_forall : bool = false
  val test_exists : bool = true
  val test_mem : bool = false
  val test_filter : int list = [4; 5]
  val test_complement : int list = [1; 3; 5; 6]
  val test_intersection : int list = [2; 4]
  val test_zip1 : (int * string) list = [(1, "a"); (2, "b"); (3, "c")]
  Check (file "valid/test_stdlib.eff", line 137, char 1):
  Call InvalidArgument "zip: length mismatch"
  - : unit = ()
  val test_unzip : int list * string list = ([1; 2; 3], ["a"; "b"; "c"])
  val test_reverse : int list = [5; 4; 3; 2; 1]
  val test_at : int list = [1; 2; 3; 4; 5; 6]
  val test_length : int = 5
  val test_head : int = 1
  Check (file "valid/test_stdlib.eff", line 149, char 1):
  Call InvalidArgument "head: empty list"
  - : unit = ()
  val test_tail : int list = [2; 3; 4]
  Check (file "valid/test_stdlib.eff", line 153, char 1):
  Call InvalidArgument "tail: empty list"
  - : unit = ()
  val test_abs : int * int * int = (5, 5, 5)
  val test_min : int = 1
  val test_max : int = 2
  val test_gcd : int = 4
  val test_lcm : int = 24
  val test_odd : bool = false
  val test_even : bool = true
  val test_id : int = 5
  val test_id_id : '_a -> '_a = <fun>
  val test_compose : int = 196
  val test_rev_apply : int = 7
  val test_fst : string = "foo"
  val test_snd : int = 4
  Check (file "valid/test_stdlib.eff", line 181, char 1):
  Call Print "Does this work?"
  - : unit = ()
  Check (file "valid/test_stdlib.eff", line 183, char 1):
  Call Print "\"How about now?\""
  - : unit = ()
  Check (file "valid/test_stdlib.eff", line 185, char 1):
  Call Print "12"
  - : unit = ()
  Check (file "valid/test_stdlib.eff", line 187, char 1):
  Call Read ()
  - : unit = ()
  ======================================================================
  valid/tydef.eff
  ----------------------------------------------------------------------
  - : bull = Tail
  - : complex = {re = 1.2; im = 2.4}
  - : int tree = Node (10, Empty, Node (20, Empty, Empty))
  - : bull = Horns <fun>
  ======================================================================
  valid/type_annotations.eff
  ----------------------------------------------------------------------
  val f : int -> int = <fun>
  val f : int -> int = <fun>
  - : int -> (int -> bool -> int) -> int = <fun>
  val f : int -> int * int = <fun>
  val g : 'a -> 'a = <fun>
  val g : int -> int = <fun>
  val g : 'a -> 'a -> 'a = <fun>
  val g : 'a -> 'a * 'a = <fun>
  val f : int -> int = <fun>
  val f : (int, 'a) cow -> int = <fun>
  val f : ('a, int) cow -> int = <fun>
  val f : (int, int) bull -> int = <fun>
  val x : int list = []
  val h : int => int = <handler>
  ======================================================================
  valid/typing.eff
  ----------------------------------------------------------------------
  - : int = 3
  - : bool = true
  - : string = "foo"
  - : unit = ()
  - : float = 4.2
  - : int * int = (3, 4)
  - : 'a list * string = ([], "foo")
  - : (string, 'a) cow = Small "brown"
  - : ('a, string) cow = Large "white"
  - : (int, string list) cow -> (string list, int) cow = <fun>
  - : (int, string) bull = {small = 5; large = "foo"}
  - : (int, 'a) bull -> int = <fun>
  - : ('a, 'b list list) bull -> 'b list list = <fun>
  - : 'a -> string = <fun>
  - : 'a -> int = <fun>
  - : 'a -> 'a = <fun>
  - : '_a -> '_a = <fun>
  - : 'a -> 'a * 'a = <fun>
  - : ('a -> 'a) * 'b list = (<fun>, [])
  - : ('_a -> '_a) * ('_b -> '_b) = (<fun>, <fun>)
  - : 'a -> 'b -> 'a = <fun>
  - : 'a list list list = [[[]]]
  - : 'a -> 'b -> 'a = <fun>
  val h : 'a -> 'a = <fun>
  - : 'a -> 'a = <fun>
-------------------------------------------------------------------------------
