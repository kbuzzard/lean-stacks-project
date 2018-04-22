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
import tag00EJ -- finite cover by basic opens sheaf axiom
universes u v w

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

instance zariski.structure_presheaf_on_standard.comm_ring {R : Type u} [comm_ring R] (U : set (X R)) (H : is_zariski.standard_open U) :
comm_ring (zariski.structure_presheaf_on_standard U H) :=
@localization.comm_ring _ _ _ (nonzero_on_U_is_mult_set U)

structure R_alg_equiv {R : Type u} {α : Type v} {β : Type w} [comm_ring R] [comm_ring α] [comm_ring β]
  (sα : R → α) (sβ : R → β) extends ring_equiv α β :=
(R_alg_hom : sβ = to_fun ∘ sα)

-- This proof could be simpler: a lot of the definitions would follow from
-- universal properties, but Kenny just proved them directly anyway.
noncomputable definition zariski.structure_presheaf_on_standard_is_loc {R : Type u} [comm_ring R] (f : R) :
  R_alg_equiv (localization.of_comm_ring R _ : R → zariski.structure_presheaf_on_standard (Spec.D'(f)) (⟨f,rfl⟩))
    (localization.of_comm_ring R (powers f) : R → localization.away f) :=  
{ to_fun      := localization.extend_map_of_im_unit
    (localization.of_comm_ring R (powers f))
    (λ s hs, lemma_standard_open_1a R _ _ hs),
  is_ring_hom := localization.extend_map_of_im_unit.is_ring_hom _ _,
  inv_fun     := localization.away.extend_map_of_im_unit
    (localization.of_comm_ring R _)
    ⟨localization.mk _ _ ⟨1, f, set.subset.refl _⟩,
     quotient.sound ⟨1, is_submonoid.one_mem _, by simp⟩⟩,
  left_inv    := @localization.unique _ _ _ _ _ _ _ _ 
    (@@is_ring_hom.comp _ _ _
       (localization.extend_map_of_im_unit.is_ring_hom _ _) _ _
       (localization.extend_map_of_im_unit.is_ring_hom _ _))
    (ring_equiv.refl _).is_ring_hom
    (by intro x; dsimp [ring_equiv.refl, equiv.refl]; rw [localization.extend_map_extends, localization.extend_map_extends]),
  right_inv   := @localization.unique _ _ _ _ _ _ _ _
    (@@is_ring_hom.comp _ _ _
       (localization.extend_map_of_im_unit.is_ring_hom _ _) _ _
       (localization.extend_map_of_im_unit.is_ring_hom _ _))
    (ring_equiv.refl _).is_ring_hom
    (by intro x; dsimp [ring_equiv.refl, equiv.refl]; rw [localization.extend_map_extends, localization.extend_map_extends]),
  R_alg_hom := (funext (λ r, (localization.extend_map_extends
     (_ : R → localization.loc R (powers f))
     _ r 
       ).symm)
  : localization.of_comm_ring R (powers f) =
    localization.extend_map_of_im_unit (localization.of_comm_ring R (powers f)) _ ∘
      localization.of_comm_ring R (non_zero_on_U (Spec.D' f)))
}

#check zariski.structure_presheaf_on_standard_is_loc

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


-- first let's check the sheaf axiom for finite covers, using the fact that 
-- the intersection of two basis opens is a basic open (meaning we can use
-- tag 009L instead of 009K).

-- this should follow from 
-- a) Chris' lemma [lemma_standard_covering₁ and ₂].
-- b) the fact (proved by Kenny) that localization of R at mult set of functions non-vanishing
--    on D(f) is isomorphic (as ring, but we will only need as ab group) to R[1/f]
-- c) the fact (which is probably done somewhere but I'm not sure where) that
--    D(f) is homeomorphic to Spec(R[1/f]) and this homeo identifies D(g) in D(f) with D(g)
--    in Spec(R[1/f]) [TODO -- check this is done!]
--
-- In other words, all the maths is done, it's just a case of glueing it together.


-- what we need for (a)
/-
#check @lemma_standard_covering₁

∀ {R : Type u_1} {γ : Type u_2} [_inst_1 : comm_ring R] [_inst_2 : fintype γ] {f : γ → R},
    1 ∈ span ↑(finset.image f finset.univ) → function.injective (α f)
▹
-/
/-
#check @lemma_standard_covering₂

  ∀ {R : Type u_1} {γ : Type u_2} [_inst_1 : comm_ring R] [_inst_2 : fintype γ] (f : γ → R),
    1 ∈ span ↑(finset.image f finset.univ) →
    ∀ (s : Π (i : γ), localization.loc R (powers (f i))), β s = 0 ↔ ∃ (r : R), α f r = s
-/
-- what we need for (b)
/-
#check zariski.structure_presheaf_on_standard_is_loc

  Π (f : ?M_1), zariski.structure_presheaf_on_standard (Spec.D' f) _ ≃ᵣ localization.away f
-/
-- what we need for (c)
/-
#check lemma_standard_open 

lemma_standard_open :
  ∀ (R : Type) [_inst_1 : comm_ring R] (f : R),
    let φ : X (localization.loc R (powers f)) → X R := Zariski.induced (localization.of_comm_ring R (powers f))
    in topological_space.open_immersion φ ∧ φ '' set.univ = Spec.D' f
-/
/-
What remains for (c): Say D(g) is an open in D(f) (both opens in Spec(R)). We want to apply Chris' Lemma
to D(g) considered as an open in Spec(R[1/f]). What can we deduce from lemma_standard_open? We know
Spec(R[1/f]) is identified with D(f) and Spec(R[1/g]) is identified with D(g). We know there's a map
R[1/f] -> R[1/g] (because of some lemma about f being invertible in R[1/g] as it doesn't vanish on D(g) -- what is this lemma?
TODO chase this up) and that this is an R-algebra map. I guess we need to prove D(g) is a basic open in Spec(R[1/f])
and this is the assertion that the pullback of D(g) to Spec(R[1/f]) equals Spec((R[1/f])[1/g-bar]) with g-bar the image of
g in R[1/f]. So that's something that needs doing. And I guess actually that should be it. I'm not sure this is helpful
but the pullback should be Spec R[1/f] tensor_R Spec R[1/g]. Hopefully we can get away without introducing tensor
products at this point. Aah! If I can construct an R[1/f]-algebra isomorphism between R[1/g] and R[1/f][1/g-bar] I'll be done.
This should all follow from the universal property.
-/

/-
#check lemma_standard_open_1c

lemma_standard_open_1c :
  Π (R : Type u_1) [_inst_1 : comm_ring R] (f g : R),
    Spec.D' g ⊆ Spec.D' f → localization.away f → localization.away g
-/

--#print notation ≃ᵣ
--#print ring_equiv -- this is in temp

-- I just put a bunch of notes on how to do this stuff in localization_UMP.lean, which
-- should be moved here.

-- some lemmas : what I need is (4). I need this to deduce the sheaf axiom
-- for finite covers of a basic open by basic opens. I need to apply the
-- standard ring theory exact sequence lemma to a localisation, and
-- (4) is, I believe, the issue that I'll have to resolve. 
/-
1) f invertible in R implies R[1/f] uniquely R-iso to R
2) R[1/f][1/g] uniquely R-iso to R[1/fg]
3) cor : g invertible in R[1/f] implies R[1/f] = R[1/fg] uniquely R-iso
4) cor : f invertible in R[1/g] implies R[1/g] = R[1/f][1/g] uniquely R-iso
-/

/-
Here's the strat:

  1)  f invertible in R implies R[1/f] uniquely R-iso to R:

There's a unique R-algebra map R[1/f] -> R from the universal property. There's a unique
 R-algebra map R -> R[1/f] -- this is trivial. Now the standard argument: composition
  gives R-algebra maps R[1/f] -> R[1/f] and R->R but again by the universal property 
  there's a unique R-algebra map R[1/f] -> R[1/f] etc etc, so it's the identity. etc etc.
   So this gives (1) without any extra lemmas or structures.

  2) R[1/f][1/g] uniquely R-iso to R[1/fg]:

Both f and g have inverses in R[1/f][1/g] so there's a unique R-alg map 
R[1/fg] -> R[1/f][1/g]. f is invertible in R[1/fg] (it's a lemma that every element
 of S has an inverse in R[1/S]) so there's a unique R-alg map R[1/f] -> R[1/fg] and 
 also a unique R[1/f]-alg map R[1/f][1/g] -> R[1/fg]. I claim that there's a unique
  R-alg map R[1/f][1/g] -> R[1/fg]. Indeed any R-alg map gives, by composition with 
  the R[1/f]-alg map R[1/f] -> R[1/f][1/g], an R-alg map R[1/f] -> R[1/fg] which must 
  be the unique one, hence our original R-alg map was an R[1/f]-alg map and hence the
   one we know.


(3) and (4) now follow (4 from 3 by switching f and g temporarily)

    cor : g invertible in R[1/f] implies R[1/f] = R[1/fg] uniquely R-iso
    cor : f invertible in R[1/g] implies R[1/g] = R[1/f][1/g] uniquely R-iso

-/

open localization 

-- everything under here needs to be re-evaluated
noncomputable definition localization.loc_loc_is_loc {R : Type u} [comm_ring R] {f g : R} (H : Spec.D' g ⊆ Spec.D' f) :
(away g) ≃ᵣ away (of_comm_ring R (powers f) g) := 
{ to_fun := away.extend_map_of_im_unit 
              (of_comm_ring (away f) _ ∘ (of_comm_ring R (powers f)) : R → loc (away f) (powers (of_comm_ring R (powers f) g)))
              sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry,
  is_ring_hom := sorry
}


theorem zariski.sheaf_of_types_on_standard_basis_for_finite_covers (R : Type u) [comm_ring R] :
  ∀ (U : set (X R)) (BU : U ∈ (standard_basis R)) (γ : Type u) (Fγ : fintype γ)
  (Ui : γ → set (X R)) (BUi :  ∀ i : γ, (Ui i) ∈ (standard_basis R))
  (Hcover: (⋃ (i : γ), (Ui i)) = U),
  sheaf_property (D_f_form_basis R) (zariski.structure_presheaf_of_types_on_basis_of_standard R)
   (λ U V ⟨f,Hf⟩ ⟨g,Hg⟩,⟨f*g,Hf.symm ▸ Hg.symm ▸ (tag00E0.lemma15 _ f g).symm⟩) U BU γ Ui BUi Hcover :=
begin
admit
end 



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
