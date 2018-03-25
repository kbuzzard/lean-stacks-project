-- here we define a presheaf of types on a basis of a top space;
-- sections only defined on a basis
-- restriction maps are just from basis elt to basis elt
-- 

import analysis.topology.topological_space

structure  presheaf_of_types_on_basis {X : Type*} [T : topological_space X] (B : set (set X)) 
  (HB : topological_space.is_topological_basis B) := 
(F : Π U : set X, B U → Type*)
(res : ∀ (U V : set X) (OU : B U) (OV : B V) (H : V ⊆ U), 
  (F U OU) → (F V OV))
(Hid : ∀ (U : set X) (OU : B U), (res U U OU OU (set.subset.refl U)) = id)  
(Hcomp : ∀ (U V W : set X) (OU : B U) (OV : B V) (OW : B W)
  (HUV : V ⊆ U) (HVW : W ⊆ V),
  (res U W OU OW (set.subset.trans HVW HUV)) = (res V W OV OW HVW) ∘ (res U V OU OV HUV) )
