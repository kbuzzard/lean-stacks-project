-- stuff mentioned in section "Bases and sheaves" (6.30; tag 009H)
-- but not in any definition etc

import tag009I 

-- definition after 6.30.1 and before 6.30.2

definition presheaf_on_basis_stalk {X : Type*} [TX : topological_space X] 
  {B : set (set X)}
  (HB : topological_space.is_topological_basis B) 
  (FPTB : presheaf_of_types_on_basis HB) (x : X) : Type :=
sorry
-- 
-- set Z is pairs (U,s) with U in B and x in U and s in FPTB.F(U)
-- equiv reln on Z : (U,s) tilde (V,t) iff there exists W in B 
-- such that x in W, W in U, W in V, and FPT.res (U to W) s = FPT.res (V to W) t
-- note basis axiom HB.1:
-- (∀t₁∈s, ∀t₂∈s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃∈s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂)
-- Will need this for transitivity

