/- Under defintion 25.5.2 (tag 01HT) and before 25.5.3 (01HU) there is an
argument which defines the sheaf of rings on Spec(R), and also the
quasicoherent sheaf
of O_X-modules attached to an R-module.
-/

/- Let's just do this for rings at this point.

-/
import group_theory.submonoid  
import ring_theory.localization 
import Kenny_comm_alg.Zariski 
import tag00E0 
import tag01HS_statement 
import tag009I -- presheaf of types on a basis
import tag00DY -- claim that D(f) form a basis
import tag006N -- presheaves / sheaves of rings on a basis
import tag009P -- presheaf of rings on a basis
import tag009L -- sheaf for finite covers on basis -> sheaf for basis

universe u

def is_zariski.standard_open {R : Type u} [comm_ring R] (U : set (X R)) := ∃ f : R, U = Spec.D'(f)

def non_zero_on_U {R : Type u} [comm_ring R] (U : set (X R)) : set R := {g : R | U ⊆ Spec.D'(g)}

instance nonzero_on_U_is_mult_set {R : Type u} [comm_ring R] (U : set (X R)) : is_submonoid (non_zero_on_U U) := 
{ one_mem := λ P HP, @is_proper_ideal.one_not_mem _ _ P.1 P.2.1,
  mul_mem := begin
    intros f g Hf Hg,
    show U ⊆ Spec.D'(f*g),
    rw [tag00E0.lemma15 R f g],
    exact set.subset_inter Hf Hg
    end
}

lemma nonzero_on_U_mono {R : Type u} [comm_ring R] {U V : set (X R)} : V ⊆ U → non_zero_on_U U ⊆ non_zero_on_U V :=
λ H _,set.subset.trans H

def zariski.structure_presheaf_on_standard {R : Type u} [comm_ring R] (U : set (X R)) (H : is_zariski.standard_open U) : Type u := 
  @localization.loc R _ (non_zero_on_U U) (nonzero_on_U_is_mult_set U)

instance zariski.structure_presheaf_on_standard.comm_ring {R : Type u} [comm_ring R] (U : set (X R)) (H : is_zariski.standard_open U) : comm_ring (zariski.structure_presheaf_on_standard U H) :=
@localization.comm_ring _ _ _ (nonzero_on_U_is_mult_set U)

-- I (KB) think we might need more here. I think we might need that the isomorphism is the unique R-algebra map between these things.
-- This might follow easily from the UMP stuff KB just added.
noncomputable lemma zariski.structure_presheaf_on_standard_is_loc {R : Type u} [comm_ring R] (f : R) :
  zariski.structure_presheaf_on_standard (Spec.D'(f)) (⟨f,rfl⟩) ≃ᵣ localization.away f :=
{ to_fun      := localization.extend_map_of_im_unit
    (localization.of_comm_ring R (powers f))
    (λ s hs, lemma_standard_open_1a R _ _ hs),
  is_ring_hom := localization.extend_map_of_im_unit.is_ring_hom _ _,
  inv_fun     := localization.away.extend_map_of_im_unit
    (localization.of_comm_ring R _)
    ⟨localization.mk _ _ ⟨1, f, set.subset.refl _⟩,
     quotient.sound ⟨1, is_submonoid.one_mem _, by simp⟩⟩,
  left_inv    := @localization.unique _ _ _ _ _ _ _ _
    (@@is_ring_hom.comp _ _ _ _ _
       (localization.extend_map_of_im_unit.is_ring_hom _ _)
       (localization.extend_map_of_im_unit.is_ring_hom _ _))
    (ring_equiv.refl _).is_ring_hom
    (by intro x; dsimp [ring_equiv.refl, equiv.refl]; rw [localization.extend_map_extends, localization.extend_map_extends]),
  right_inv   := @localization.unique _ _ _ _ _ _ _ _
    (@@is_ring_hom.comp _ _ _ _ _
       (localization.extend_map_of_im_unit.is_ring_hom _ _)
       (localization.extend_map_of_im_unit.is_ring_hom _ _))
    (ring_equiv.refl _).is_ring_hom
    (by intro x; dsimp [ring_equiv.refl, equiv.refl]; rw [localization.extend_map_extends, localization.extend_map_extends]) }

-- -> mathlib?
instance is_comm_ring_hom.id {α : Type u} [comm_ring α] : is_ring_hom (@id α) :=
{map_add := λ _ _,rfl,map_mul := λ _ _,rfl,map_one := rfl}

-- -> mathlib?
universes v w
instance is_comm_ring_hom.comp {α : Type u} {β : Type v} {γ : Type w} [comm_ring α] [comm_ring β] [comm_ring γ]
{f : α → β} {g : β → γ} [Hf : is_ring_hom f] [Hg : is_ring_hom g] : is_ring_hom (g ∘ f) :=
{ map_add := λ x y,by simp [Hf.map_add,Hg.map_add],
  map_mul := λ x y, by simp [Hf.map_mul,Hg.map_mul],
  map_one := show g (f 1) = 1, by rw [Hf.map_one, Hg.map_one]
}

-- just under Definition 25.5.2

-- Definition of presheaf-of-sets on basis
noncomputable definition zariski.structure_presheaf_of_types_on_basis_of_standard (R : Type u) [comm_ring R]
: presheaf_of_types_on_basis (D_f_form_basis R) := 
{ F := zariski.structure_presheaf_on_standard,
  res := λ _ _ _ _ H,localization.localize_superset (nonzero_on_U_mono H),
  Hid := λ _ _,eq.symm (localization.localize_superset.unique_algebra_hom _ _ (λ _,rfl)),
  Hcomp := λ _ _ _ _ _ _ _ _,eq.symm (localization.localize_superset.unique_algebra_hom _ _ (
    λ r, by simp [localization.localize_superset.is_algebra_hom]
  ))
}

-- now let's make it a presheaf of rings on the basis
noncomputable definition zariski.structure_presheaf_of_rings_on_basis_of_standard (R : Type u) [comm_ring R]
: presheaf_of_rings_on_basis (D_f_form_basis R) :=
{ Fring := zariski.structure_presheaf_on_standard.comm_ring,
  res_is_ring_morphism := λ _ _ _ _ _,localization.localize_superset.is_ring_hom _,
  ..zariski.structure_presheaf_of_types_on_basis_of_standard R,
}

-- computation of stalk: I already did this for R I think.

-- now let's prove it's a sheaf of rings on the basis

-- first let's check the sheaf axiom for finite covers.

theorem zariski.sheaf_of_types_on_standard_basis_for_finite_covers (R : Type u) [comm_ring R] :
  ∀ (U : set (X R)) (BU : U ∈ (standard_basis R)) (γ : Type u) (Fγ : fintype γ)
  (Ui : γ → set (X R)) (BUi :  ∀ i : γ, (Ui i) ∈ (standard_basis R))
  (Hcover: (⋃ (i : γ), (Ui i)) = U),
  sheaf_property (D_f_form_basis R) (zariski.structure_presheaf_of_types_on_basis_of_standard R)
   (λ U V BU BV,sorry) U BU γ Ui BUi Hcover := sorry
-- this is Chris' lemma.

theorem zariski.structure_sheaf_of_rings_on_basis_of_standard (R : Type u) [comm_ring R] : 
is_sheaf_of_rings_on_basis (zariski.structure_presheaf_of_rings_on_basis_of_standard R) :=
begin
  intros U BU,  
  -- follows from lemma_cofinal_systems_coverings_standard_case
  -- applied to zariski.sheaf_of_types_on_standard_basis_for_finite_covers
  admit,
end


-- now prove it's a sheaf of rings on the full topology.
-- it's tag009N which should basically be done
