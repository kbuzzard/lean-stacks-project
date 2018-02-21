/-
This is a section.
It contains 00DZ, 00E0, 00E1 and 00E2 and 00E3 and 00E4 and 00E5 and 00E6 and 00E7 and 00E8 and 04PM

It also contains the following useful claim, just under Lemma 10.16.2 (tag 00E0):

The sets D(f) are open and form a basis for this topology (on Spec(R))

-/

import Kenny_comm_alg.temp analysis.topology.topological_space Kenny_comm_alg.Zariski

universe u 
variables α : Type u
variable t : topological_space α 
#check t 
#print topological_space 

def topological_space.is_topological_basis' {α : Type u} [t : topological_space α] (s : set (set α)) :=
(∀ U : set α, U ∈ s → t.is_open U) ∧ 
(∀ U : set α, t.is_open U → (∀ x, x ∈ U → ∃ V : set α, V ∈ s ∧ x ∈ V ∧ V ⊆ U))

#print topological_space.generate_open

lemma basis_is_basis' {α : Type u} [t : topological_space α] (s : set (set α)) : 
  topological_space.is_topological_basis s ↔ topological_space.is_topological_basis' s :=
begin
  split,
  { intro H,
    split,
    { intros U HU,
      rw H.right.right,
      exact topological_space.generate_open.basic U HU },
    { intros U HU x Hx,
      unfold topological_space.is_topological_basis at H,
      have H2 := H.2.2,
      rw H2 at HU,
      have H3 : topological_space.generate_open s U := HU,
      induction H3 with U4 H5 U6 U7 H8 H9 H10 H11 UU12 H13 H14,
      { existsi U4,
        split,exact H5,
        split,exact Hx,
        exact set.subset.refl U4
      },
      { have H4 := H.2.1,
        have H5 : (⋃₀ s) x,
          rw H4,unfold set.univ,
        cases H5 with V HV,
        cases HV with H6 H7,
        existsi V,
        split,exact H6,
        split,exact H7,
        exact set.subset_univ V,
      },
      { have H12 := H10 (set.inter_subset_left U6 U7 Hx) H8,
        have H13 := H11 (set.inter_subset_right U6 U7 Hx) H9,
        cases H12 with V14 H14,
        cases H13 with V15 H15,
        have H16 := H.1 V14 H14.1 V15 H15.1 x ⟨H14.2.1,H15.2.1⟩,
        cases H16 with V H17,
        cases H17 with H18 H19, 
        existsi V,
        split,exact H18,
        split,exact H19.1,
        refine set.subset.trans H19.2 _,
        exact set.inter_subset_inter H14.2.2 H15.2.2,

      },
      { cases Hx with V HV,
        cases HV with H15 H16,
        
      },
         
    }
  },
  admit,
end 


lemma D_f_form_basis (R : Type) [comm_ring R] : 
  topological_space.is_topological_basis {U : set (X R) | ∃ f : R, U = Spec.D'(f)} := 
begin
unfold topological_space.is_topological_basis,
split,
intros U HU,
cases HU with f Hf,
intros V HV,

end
