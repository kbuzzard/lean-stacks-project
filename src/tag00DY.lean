/-
This is a section.
It contains 00DZ, 00E0, 00E1 and 00E2 and 00E3 and 00E4 and 00E5 and 00E6 and 00E7 and 00E8 and 04PM

It also contains the following useful claim, just under Lemma 10.16.2 (tag 00E0):

The sets D(f) are open and form a basis for this topology (on Spec(R))

-/

import Kenny_comm_alg.temp Kenny_comm_alg.Zariski

local attribute [instance] classical.prop_decidable

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
    rw not_forall at H3,
    cases H3 with f H3,
    rw not_imp at H3,
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