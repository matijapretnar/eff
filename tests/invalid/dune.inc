(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "duplicate_field_tydef_record.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./duplicate_field_tydef_record.eff")))))

(rule
 (alias runtest)
  (action
   (diff "duplicate_field_tydef_record.eff.ref" "duplicate_field_tydef_record.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "duplicate_let.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./duplicate_let.eff")))))

(rule
 (alias runtest)
  (action
   (diff "duplicate_let.eff.ref" "duplicate_let.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "duplicate_let_toplevel.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./duplicate_let_toplevel.eff")))))

(rule
 (alias runtest)
  (action
   (diff "duplicate_let_toplevel.eff.ref" "duplicate_let_toplevel.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "duplicate_operation_tydef_effect.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./duplicate_operation_tydef_effect.eff")))))

(rule
 (alias runtest)
  (action
   (diff "duplicate_operation_tydef_effect.eff.ref" "duplicate_operation_tydef_effect.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "duplicate_variant_tydef_sum.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./duplicate_variant_tydef_sum.eff")))))

(rule
 (alias runtest)
  (action
   (diff "duplicate_variant_tydef_sum.eff.ref" "duplicate_variant_tydef_sum.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "less_than_complex.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./less_than_complex.eff")))))

(rule
 (alias runtest)
  (action
   (diff "less_than_complex.eff.ref" "less_than_complex.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "less_than_function.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./less_than_function.eff")))))

(rule
 (alias runtest)
  (action
   (diff "less_than_function.eff.ref" "less_than_function.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "less_than_handler.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./less_than_handler.eff")))))

(rule
 (alias runtest)
  (action
   (diff "less_than_handler.eff.ref" "less_than_handler.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "malformed_type_application.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./malformed_type_application.eff")))))

(rule
 (alias runtest)
  (action
   (diff "malformed_type_application.eff.ref" "malformed_type_application.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "non_linear_pattern.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./non_linear_pattern.eff")))))

(rule
 (alias runtest)
  (action
   (diff "non_linear_pattern.eff.ref" "non_linear_pattern.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "non_linear_record.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./non_linear_record.eff")))))

(rule
 (alias runtest)
  (action
   (diff "non_linear_record.eff.ref" "non_linear_record.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "occurs_check.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./occurs_check.eff")))))

(rule
 (alias runtest)
  (action
   (diff "occurs_check.eff.ref" "occurs_check.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "polymorphism_id_id.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./polymorphism_id_id.eff")))))

(rule
 (alias runtest)
  (action
   (diff "polymorphism_id_id.eff.ref" "polymorphism_id_id.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "shadow_eff.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./shadow_eff.eff")))))

(rule
 (alias runtest)
  (action
   (diff "shadow_eff.eff.ref" "shadow_eff.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "shadow_field.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./shadow_field.eff")))))

(rule
 (alias runtest)
  (action
   (diff "shadow_field.eff.ref" "shadow_field.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "shadow_label.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./shadow_label.eff")))))

(rule
 (alias runtest)
  (action
   (diff "shadow_label.eff.ref" "shadow_label.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "shadow_type.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./shadow_type.eff")))))

(rule
 (alias runtest)
  (action
   (diff "shadow_type.eff.ref" "shadow_type.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "use_undefined_type.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       1
       (run eff "./use_undefined_type.eff")))))

(rule
 (alias runtest)
  (action
   (diff "use_undefined_type.eff.ref" "use_undefined_type.eff.out")))

