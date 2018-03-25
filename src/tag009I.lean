-- here we define a presheaf of types on a basis of a top space;
-- sections only defined on a basis
-- restriction maps are just from basis elt to basis elt
-- 

import analysis.topology.topological_space

structure presheaf_of_types_on_basis {X : Type*} [TX : topological_space X] {B : set (set X)}
  (HB : topological_space.is_topological_basis B) := 
(F : Π U : set X, B U → Type*)
(res : ∀ {U V : set X} (OU : B U) (OV : B V) (H : V ⊆ U), 
  (F U OU) → (F V OV))
(Hid : ∀ (U : set X) (OU : B U), (res OU OU (set.subset.refl U)) = id)  
(Hcomp : ∀ (U V W : set X) (OU : B U) (OV : B V) (OW : B W)
  (HUV : V ⊆ U) (HVW : W ⊆ V),
  (res OU OW (set.subset.trans HVW HUV)) = (res OV OW HVW) ∘ (res OU OV HUV) )


structure morphism_of_presheaves_of_types_on_basis {X : Type*} [TX : topological_space X] 
  (B : set (set X)) (HB : topological_space.is_topological_basis B)
  (FPT : presheaf_of_types_on_basis HB) 
  (GPT : presheaf_of_types_on_basis HB) 
  :=
(morphism : ∀ U : set X, ∀ HU : B U, (FPT.F U HU) → GPT.F U HU)
(commutes : ∀ U V : set X, ∀ HU : B U, ∀ HV : B V, ∀ Hsub : V ⊆ U,
  (GPT.res HU HV Hsub) ∘ (morphism U HU) = (morphism V HV) ∘ (FPT.res HU HV Hsub))
