/- Under defintion 25.5.2 (tag 01HT) and before 25.5.3 (01HU) there is an
argument which defines the sheaf of rings on Spec(R), and also the
quasicoherent sheaf
of O_X-modules attached to an R-module.
-/

/- Let's just do this for rings at this point.

-/
import Kenny_comm_alg.Zariski localization tag00E0 tag01HS_statement
universe u

#check tag00E0.lemma15
#print is_prime_ideal

def is_zariski.standard_open {R : Type u} [comm_ring R] (U : set (X R)) := ∃ f : R, U = Spec.D'(f)

instance nonzero_on_U_is_mult_set {R : Type u} [comm_ring R] (U : set (X R)) : is_submonoid R {g : R | U ⊆ Spec.D'(g)} := 
{ one_mem := λ P HP, @is_proper_ideal.one_not_mem _ _ P.1 P.2.1,
  mul_mem := begin
    intros f g Hf Hg,
    show U ⊆ Spec.D'(f*g),
    rw [tag00E0.lemma15 R f g],
    exact set.subset_inter Hf Hg
    end
}

def zariski.structure_sheaf_standard {R : Type u} [comm_ring R] (U : set (X R)) (H : is_zariski.standard_open U) : Type u := 
  @localization.loc R _ {g : R | U ⊆ Spec.D'(g)} (nonzero_on_U_is_mult_set U)

instance zariski.structure_sheaf_standard.comm_ring {R : Type u} [comm_ring R] (U : set (X R)) (H : is_zariski.standard_open U) : comm_ring (zariski.structure_sheaf_standard U H) :=
@localization.comm_ring _ _ _ (nonzero_on_U_is_mult_set U)

noncomputable lemma zariski.structure_sheaf_on_standard {R : Type u} [comm_ring R] (f : R) :
  zariski.structure_sheaf_standard (Spec.D'(f)) (⟨f,rfl⟩) ≃ᵣ localization.away f :=
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