-- here we define a presheaf of types on a basis of a top space;
-- sections only defined on a basis
-- restriction maps are just from basis elt to basis elt
-- 

import analysis.topology.topological_space
universe u 

structure presheaf_of_types_on_basis {X : Type u} [TX : topological_space X] {B : set (set X)}
  (HB : topological_space.is_topological_basis B) := 
(F : Π {U : set X}, U ∈ B → Type u)
(res : ∀ {U V : set X} (BU : U ∈ B) (BV : V ∈ B) (H : V ⊆ U), 
  (F BU) → (F BV))
(Hid : ∀ (U : set X) (BU : U ∈ B), (res BU BU (set.subset.refl U)) = id)  
(Hcomp : ∀ (U V W : set X) (BU : U ∈ B) (BV : V ∈ B) (BW : W ∈ B)
  (HUV : V ⊆ U) (HVW : W ⊆ V),
  (res BU BW (set.subset.trans HVW HUV)) = (res BV BW HVW) ∘ (res BU BV HUV) )


structure morphism_of_presheaves_of_types_on_basis {X : Type u} [TX : topological_space X] 
  {B : set (set X)} {HB : topological_space.is_topological_basis B}
  (FPT : presheaf_of_types_on_basis HB) 
  (GPT : presheaf_of_types_on_basis HB) 
  :=
(morphism : ∀ {U} (HU : U ∈ B), (FPT.F HU) → GPT.F HU)
(commutes : ∀ {U V} (HU : U ∈ B) (HV : V ∈ B) (Hsub : V ⊆ U),
  (GPT.res HU HV Hsub) ∘ (morphism HU) = (morphism HV) ∘ (FPT.res HU HV Hsub))

definition composition_of_morphism_of_presheaves_of_types_on_basis
{X : Type u} [TX : topological_space X] 
  {B : set (set X)} {HB : topological_space.is_topological_basis B}
  {FPT : presheaf_of_types_on_basis HB} 
  {GPT : presheaf_of_types_on_basis HB} 
  {HPT : presheaf_of_types_on_basis HB}
  (phi : morphism_of_presheaves_of_types_on_basis FPT GPT)
  (psi : morphism_of_presheaves_of_types_on_basis GPT HPT)
  : morphism_of_presheaves_of_types_on_basis FPT HPT :=
{
  morphism := λ U HU, (psi.morphism HU) ∘ (phi.morphism HU),
  commutes := λ U V HU HV Hsub,
  by rw [←function.comp.assoc,psi.commutes,function.comp.assoc,phi.commutes],
}

definition is_identity_morphism_of_presheaves_of_types_on_basis {X : Type u} [TX : topological_space X] 
  {B : set (set X)} {HB : topological_space.is_topological_basis B}
  {FPT : presheaf_of_types_on_basis HB} (phi : morphism_of_presheaves_of_types_on_basis FPT FPT)
  : Prop :=
  ∀ U : set X, ∀ HU : U ∈ B, phi.morphism HU = id 

definition is_isomorphism_of_presheaves_of_types_on_basis 
{X : Type u} [TX : topological_space X] 
  {B : set (set X)} {HB : topological_space.is_topological_basis B}
  {FPT : presheaf_of_types_on_basis HB}
  {GPT : presheaf_of_types_on_basis HB}
  (phi : morphism_of_presheaves_of_types_on_basis FPT GPT) : Prop := 
  ∃ psi :  morphism_of_presheaves_of_types_on_basis GPT FPT,
  is_identity_morphism_of_presheaves_of_types_on_basis (composition_of_morphism_of_presheaves_of_types_on_basis phi psi)
  ∧ is_identity_morphism_of_presheaves_of_types_on_basis (composition_of_morphism_of_presheaves_of_types_on_basis psi phi)
