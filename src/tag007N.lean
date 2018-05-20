-- current half-baked plan is to check basic opens containig x in Spec(R) are a directed set
-- and to try and glue everything together.
-- This is not really tag007N at all and it imports some much later tags.
-- It's the proof that the stalks of the structure sheaf on the basis are sheaves of rings.

import Kenny_comm_alg.direct_limit
import analysis.topology.topological_space
import Kenny_comm_alg.Zariski
import tag00DY -- standard basis 
import tag00E0 -- intersection of two basis elements is a basis elt
import tag01HR 

universe u 

variables {R : Type u} [comm_ring R]

definition basis_nhds (x : X R)
:= {U : set (X R) // x ∈ U ∧ U ∈ standard_basis R} 

instance basis_nhds_has_le (x : X R) :
has_le (basis_nhds x) := ⟨λ Us Vs,Vs.1 ⊆ Us.1⟩ 

instance basis_nhds_is_partial_order (x : X R) :
partial_order (basis_nhds x) := 
{ le := (≤),
  le_refl := λ Us, set.subset.refl Us.1,
  le_trans := λ Us Vs Ws HUV HVW, set.subset.trans HVW HUV,
  le_antisymm := λ Us Vs HUV HVU, subtype.eq $ set.subset.antisymm HVU HUV
}

/-
theorem basis_nhds_directed (x : X R) :
∀ U V : basis_nhds x, ∃ W : basis_nhds x, U ≤ W ∧ V ≤ W :=
λ U V,
let ⟨W,HW⟩ := HB.1 U.1 U.2.2 V.1 V.2.2 x ⟨U.2.1,V.2.1⟩ in 
⟨⟨W,HW.snd.1,HW.fst⟩,
  set.subset.trans HW.snd.2 (set.inter_subset_left _ _),
  set.subset.trans HW.snd.2 (set.inter_subset_right _ _)
⟩
-/
-- This is already in, in a later tag (01HR). Needs to go somewhere sane.
lemma zariski.standard_basis_has_FIP' (R : Type u) [comm_ring R] : ∀ (U V : set (X R)),
  U ∈ (standard_basis R) → V ∈ (standard_basis R) → U ∩ V ∈ (standard_basis R) :=
λ U V ⟨f,Hf⟩ ⟨g,Hg⟩,⟨f*g,Hf.symm ▸ Hg.symm ▸ (tag00E0.lemma15 _ f g).symm⟩


instance basis_nhds_has_sup (x : X R) :
lattice.has_sup (basis_nhds x) := {
  sup := λ Us Vs, ⟨Us.1 ∩ Vs.1,⟨Us.2.1,Vs.2.1⟩,zariski.standard_basis_has_FIP' R _ _ Us.2.2 Vs.2.2⟩
}

#check @directed_system 

definition stalk_directed_system (x : X R) : 
  @directed_system _ _ _ _ (λ (Us Vs : basis_nhds x) HUV,
     (zariski.structure_presheaf_of_rings_on_basis_of_standard R).res Us.2.2 Vs.2.2 HUV) := sorry 

#exit
    basis_nhds_are_directed_set (x : X R) : directed_order (basis_nhds x) :=
{ le_sup_left := begin end,
  le_sup_right := sorry
}

end topological_space 
-/
-/
end presheaf_on_basis_stalk
