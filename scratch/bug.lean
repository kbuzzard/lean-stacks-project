structure presheaf_of_types := 
(res : unit → unit)
(Hidem : ∀ U : unit, res = res ∘ res)

set_option trace.type_context.is_def_eq_detail true

definition presheaf_of_types_pushforward
  : presheaf_of_types :=
  { 
      Hidem := λ U, rfl,
       }