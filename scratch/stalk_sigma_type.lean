-- stuff mentioned in section "Bases and sheaves" (6.30; tag 009H)
-- but not in any definition etc

import tag009I 

-- definition after 6.30.1 and before 6.30.2

section presheaf_on_basis_stalk 

parameters {X : Type*} [TX : topological_space X] 
  {B : set (set X)}
  {HB : topological_space.is_topological_basis B}
  (FPTB : presheaf_of_types_on_basis HB) (x : X)

structure presheaf_on_basis_stalk.aux :=
(U : set X)
(BU : U ∈ B)
(Hx : x ∈ U)
(s : FPTB.F BU)

instance presheaf_on_basis_stalk.setoid : setoid presheaf_on_basis_stalk.aux :=
{ r := sorry,
  iseqv := sorry
}

definition presheaf_on_basis_stalk : Type* :=
quotient presheaf_on_basis_stalk.setoid

#check presheaf_on_basis_stalk 

end presheaf_on_basis_stalk

#check presheaf_on_basis_stalk 
