  $ for f in invalid/*.eff
  > do
  >   echo "======================================================================"
  >   echo $f
  >   echo "----------------------------------------------------------------------"
  >   ../eff.exe $f
  > done
  ======================================================================
  invalid/duplicate_field_tydef_record.eff
  ----------------------------------------------------------------------
  Typing error (file "invalid/duplicate_field_tydef_record.eff", line 2, char 1):
  Field labels in a record type must be distinct
  ======================================================================
  invalid/duplicate_let.eff
  ----------------------------------------------------------------------
  Syntax error (file "invalid/duplicate_let.eff", line 1, char 5):
  Several definitions of x
  ======================================================================
  invalid/duplicate_let_toplevel.eff
  ----------------------------------------------------------------------
  Syntax error (file "invalid/duplicate_let_toplevel.eff", line 1, char 5):
  Several definitions of x
  ======================================================================
  invalid/duplicate_operation_tydef_effect.eff
  ----------------------------------------------------------------------
  Syntax error (file "invalid/duplicate_operation_tydef_effect.eff", line 3, char 1):
  parser error
  ======================================================================
  invalid/duplicate_variant_tydef_sum.eff
  ----------------------------------------------------------------------
  Typing error (file "invalid/duplicate_variant_tydef_sum.eff", line 2, char 1):
  Constructors of a sum type must be distinct
  ======================================================================
  invalid/invalid_match_type.eff
  ----------------------------------------------------------------------
  Typing error (file "invalid/invalid_match_type.eff", line 5, char 7):
  This expression has type a list but it should have type b.
  ======================================================================
  invalid/less_than_complex.eff
  ----------------------------------------------------------------------
  val h : 'a => 'a = <handler>
  val g : 'a => 'a = <handler>
  Runtime error: invalid comparison with <
  ======================================================================
  invalid/less_than_function.eff
  ----------------------------------------------------------------------
  Runtime error: invalid comparison with <
  ======================================================================
  invalid/less_than_handler.eff
  ----------------------------------------------------------------------
  Runtime error: invalid comparison with <
  ======================================================================
  invalid/malformed_type_application.eff
  ----------------------------------------------------------------------
  Typing error (file "invalid/malformed_type_application.eff", line 3, char 1):
  The type constructor foo expects 1 arguments
  ======================================================================
  invalid/non_linear_pattern.eff
  ----------------------------------------------------------------------
  Syntax error (file "invalid/non_linear_pattern.eff", line 2, char 5):
  Variable a occurs more than once in a pattern
  ======================================================================
  invalid/non_linear_record.eff
  ----------------------------------------------------------------------
  Syntax error (file "invalid/non_linear_record.eff", line 3, char 9):
  Fields in a record must be distinct
  ======================================================================
  invalid/occurs_check.eff
  ----------------------------------------------------------------------
  Typing error (file "invalid/occurs_check.eff", line 1, char 15):
  This expression has a forbidden cyclic type '_a = '_b -> '_a.
  ======================================================================
  invalid/polymorphism_id_id.eff
  ----------------------------------------------------------------------
  val u : 'a -> 'a = <fun>
  val v : '_a -> '_a = <fun>
  Typing error (file "invalid/polymorphism_id_id.eff", line 3, char 8):
  This expression has type string but it should have type int.
  ======================================================================
  invalid/shadow_eff.eff
  ----------------------------------------------------------------------
  Typing error: Effect A already defined.
  ======================================================================
  invalid/shadow_field.eff
  ----------------------------------------------------------------------
  Typing error (file "invalid/shadow_field.eff", line 2, char 1):
  Record field label horn is already used in type cow
  ======================================================================
  invalid/shadow_label.eff
  ----------------------------------------------------------------------
  Typing error (file "invalid/shadow_label.eff", line 2, char 1):
  Constructor Horn is already used in type cow
  ======================================================================
  invalid/shadow_type.eff
  ----------------------------------------------------------------------
  Typing error (file "invalid/shadow_type.eff", line 3, char 1):
  Type cow already defined.
  ======================================================================
  invalid/use_undefined_type.eff
  ----------------------------------------------------------------------
  Typing error (file "invalid/use_undefined_type.eff", line 1, char 1):
  Unknown type bar
  [1]
-------------------------------------------------------------------------------
