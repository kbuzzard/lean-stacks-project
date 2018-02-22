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

lemma topological.generate_from_apply {α : Type u} [t : topological_space α] (s : set (set α)) (U : set α) :
  topological_space.is_open (topological_space.generate_from s) U ↔ topological_space.generate_open s U := iff.rfl

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
      rw H.2.2 at HU,
      have H3 : topological_space.generate_open s U := HU,
      induction H3 with U4 H5 U6 U7 H8 H9 H10 H11 UU12 H13 H14,
      { existsi U4,
        split,exact H5,
        split,exact Hx,
        exact set.subset.refl U4
      },
      { have H4 := H.2.1,
        have H5 : x ∈ ⋃₀ s,
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
        rcases H14 V H15 H16 (H13 V H15) with ⟨W, H17, H18, H19⟩,
        exact ⟨W, H17, H18, set.subset.trans H19 $ set.subset_sUnion_of_mem H15⟩
      }
    }
  },
  { intro H,
    split,
    { intros U1 H1 U2 H2 x H3,
      have H4 := H.1 U1 H1,
      have H5 := H.1 U2 H2,
      have H6 := H.2 (U1 ∩ U2) (topological_space.is_open_inter t U1 U2 H4 H5) x H3,
      rcases H6 with ⟨V, H7, H8, H9⟩,
      exact ⟨V, H7, H8, H9⟩
    },
    split,
    { apply set.eq_univ_of_forall,
      intro x,
      have H1 := H.2 set.univ (topological_space.is_open_univ t) x trivial,
      rcases H1 with ⟨V, H2, H3, H4⟩,
      existsi V,
      existsi H2,
      exact H3
    },
    { apply topological_space_eq,
      apply funext,
      intro U,
      apply propext,
      rw topological.generate_from_apply,
      split,
      { intro H1,
        have H2 := H.2 U H1,
        have H3 : U = ⋃₀ {V | ∃ x ∈ U, V ∈ s ∧ x ∈ V ∧ V ⊆ U},
        { apply set.ext,
          intro x,
          split,
          { intro H3,
            have H4 := H2 x H3,
            rcases H4 with ⟨V, H4⟩,
            existsi V,
            fapply exists.intro,
            exact ⟨x, H3, H4⟩,
            exact H4.2.1
          },
          { intro H3,
            rcases H3 with ⟨U1, H3, H4⟩,
            rcases H3 with ⟨y, H3, H5, H6, H7⟩,
            exact H7 H4
          }
        },
        rw H3,
        apply topological_space.generate_open.sUnion,
        intros U1 H4,
        rcases H4 with ⟨U1, H4, H5, H6, H7⟩,
        apply topological_space.generate_open.basic,
        exact H5
      },
      { exact generate_from_le H.1 U }
    }
  }
end 


lemma D_f_form_basis (R : Type) [comm_ring R] : 
  topological_space.is_topological_basis {U : set (X R) | ∃ f : R, U = Spec.D'(f)} := 
begin
  rw basis_is_basis',
  split,
  { intros U H,
    cases H with f Hf,
    existsi ({f} : set R),
    rw Hf,
    unfold Spec.D',
    unfold Spec.V,
    unfold Spec.V',
    rw set.compl_compl,
    simp
  },
  { intros U H x H1,
    cases H with U1 H,
    have H2 : U = -Spec.V U1,
    { rw [H, set.compl_compl] },
    rw set.set_eq_def at H2,
    have H3 := H2 x,
    rw iff_true_left H1 at H3,
    simp [Spec.V, has_subset.subset, set.subset] at H3,
    rw classical.not_forall at H3,
    cases H3 with f H3,
    rw @@not_imp (classical.prop_decidable _) at H3,
    cases H3 with H3 H4,
    existsi Spec.D' f,
    split,
    { existsi f,
      refl
    },
    split,
    { exact H4 },
    { intros y H5,
      rw H2,
      intro H6,
      apply H5,
      exact H6 H3
    }
  }
end