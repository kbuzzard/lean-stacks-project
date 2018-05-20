import Kenny_comm_alg.direct_limit
import analysis.topology.topological_space
universe u 
namespace topological_space
variables {X : Type u} [topological_space X] {B : set (set X)}

definition basis_nhds 
(HB : topological_space.is_topological_basis B) (x : X) := 
{U : set X // x ∈ U ∧ U ∈ B} 

instance basis_nhds_has_le (HB : topological_space.is_topological_basis B) (x : X) :
has_le (basis_nhds HB x) := ⟨λ Us Vs,Vs.1 ⊆ Us.1⟩ 

instance basis_nhds_is_partial_order (HB : topological_space.is_topological_basis B) (x : X) :
partial_order (basis_nhds HB x) := 
{ le := (≤),
  le_refl := λ Us, set.subset.refl Us.1,
  le_trans := λ Us Vs Ws HUV HVW, set.subset.trans HVW HUV,
  le_antisymm := λ Us Vs HUV HVU, subtype.eq $ set.subset.antisymm HVU HUV
}
-- HB.1
-- (∀t₁∈s, ∀t₂∈s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃∈s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂)
theorem basis_nhds_directed 
(HB : topological_space.is_topological_basis B) (x : X) :
∀ U V : basis_nhds HB x, ∃ W, U ≤ W ∧ V ≤ W :=
λ U V,
let ⟨W,HW⟩ := HB.1 U.1 U.2.2 V.1 V.2.2 x ⟨U.2.1,V.2.1⟩ in 
⟨⟨W,HW.snd.1,HW.fst⟩,
  set.subset.trans HW.snd.2 (set.inter_subset_left _ _),
  set.subset.trans HW.snd.2 (set.inter_subset_right _ _)
⟩

#check directed_on

/-noncomputable instance basis_nhds_has_so_called_sup (HB : topological_space.is_topological_basis B) (x : X) :
lattice.has_sup (basis_nhds HB x) := {
  sup := λ Us Vs, begin
    cases (classical.indefinite_description _ (HB.1 Us.1 Us.2.2 Vs.1 Vs.2.2 x ⟨Us.2.1,Vs.2.1⟩))
      with W HW,
    cases (classical.indefinite_description _ HW) with HB HW,
    exact ⟨W,⟨HW.1,HB⟩⟩
  end 
}
-/

#exit
#check subtype

noncomputable theorem basis_nhds_are_directed_set {X : Type u} [topological_space X] {B : set (set X)} (HB : topological_space.is_topological_basis B)
(x : X) : directed_order (basis_nhds HB x) :=
{ le_sup_left := begin end,
  le_sup_right := sorry
}

end topological_space 
-/
-/
end presheaf_on_basis_stalk
