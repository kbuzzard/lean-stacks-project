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
import tag00EJ
import tag01HS_statement 
import tag009I -- presheaf of types on a basis
import tag00DY -- claim that D(f) form a basis
import tag006N -- presheaves / sheaves of rings on a basis
import tag009P -- presheaf of rings on a basis
import tag009L -- sheaf for finite covers on basis -> sheaf for basis
import data.equiv 
import canonical_isomorphism_nonsense

universes u v w uu

open localization -- should have done this ages ago



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

/-
-- warm-up: I never use this.
-- f invertible in R implies R[1/f] uniquely R-iso to R
noncomputable definition localization.loc_unit {R : Type u} [comm_ring R] (f : R) (H : is_unit f) : 
R_alg_equiv (id : R → R) (of_comm_ring R (powers f)) := 
R_alg_equiv.of_unique_homs 
  (unique_R_alg_from_R (of_comm_ring R (powers f)))
  (away_universal_property f id H)
  (unique_R_alg_from_R id)
  (id_unique_R_alg_from_loc _) 

-/

lemma tag01HR.unitf {R : Type u} [comm_ring R] (f g : R) : is_unit (of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)) (of_comm_ring R (powers f) f)) :=
im_unit_of_unit (of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g))) $ unit_of_in_S $ away.in_powers f 

lemma tag01HR.unitg {R : Type u} [comm_ring R] (f g : R) : is_unit (of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)) (of_comm_ring R (powers f) g)) :=
unit_of_in_S (away.in_powers (of_comm_ring R (powers f) g))

lemma prod_unit {R : Type u} [comm_ring R] {f g : R} : is_unit f → is_unit g → is_unit (f * g) := λ ⟨u,Hu⟩ ⟨v,Hv⟩, ⟨u*v,by rw [mul_comm u,mul_assoc f,←mul_assoc g,Hv,one_mul,Hu]⟩

lemma tag01HR.unitfg {R : Type u} [comm_ring R] (f g : R) : is_unit (of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)) (of_comm_ring R (powers f) (f * g))) :=
begin 
  have H := prod_unit (tag01HR.unitf f g) (tag01HR.unitg f g),
  let φ := of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)),
  have Hφ : is_ring_hom φ := by apply_instance,
  rw ←Hφ.map_mul at H,
  let ψ := of_comm_ring R (powers f),
  have Hψ : is_ring_hom ψ := by apply_instance,
  rw ←Hψ.map_mul at H,
  exact H
end 

/-
set_option class.instance_max_depth 93
-- I don't use the next theorem, it was just a test for whether I had the right universal properties.
noncomputable definition loc_is_loc_loc {R : Type u} [comm_ring R] (f g : R) :
R_alg_equiv 
  ((of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)))
  ∘ (of_comm_ring R (powers f)))
  (of_comm_ring R (powers (f * g))) :=
R_alg_equiv.of_unique_homs
  (away_away_universal_property' f g (of_comm_ring R (powers (f * g)))
    (unit_of_loc_more_left f g) -- proof that f is aunit in R[1/fg]
    (unit_of_loc_more_right f g) -- proof that g is a unit in R[1/fg]
  )
  (away_universal_property (f*g) 
    ((of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g))) 
      ∘ (of_comm_ring R (powers f)))
    (tag01HR.unitfg f g) -- proof that fg is a unit in R[1/f][1/g]
  )
  (away_away_universal_property' f g ((of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g))) ∘ (of_comm_ring R (powers f)))
    (tag01HR.unitf f g) -- proof that f is a unit in R[1/f][1/g]
    (tag01HR.unitg f g) -- proof that g is a unit in R[1/f][1/g]
  )
  (id_unique_R_alg_from_loc _)
-/

-- cover of a standard open translates into a cover of Spec(localization)
theorem cover_of_cover_standard {R : Type u} [comm_ring R] {r : R}
{γ : Type u} (f : γ → R) (Hcover : (⋃ (i : γ), Spec.D' (f i)) = Spec.D' r)
: (⋃ (i : γ), Spec.D' (of_comm_ring R (powers r) (f i))) = set.univ :=
set.eq_univ_of_univ_subset (λ Pr HPr, 
begin
  let φ := Zariski.induced (of_comm_ring R (powers r)),
  let P := φ Pr,
  have H : P ∈ Spec.D' r,
    rw ←(lemma_standard_open R r).2,
    existsi Pr,simp,
  rw ←Hcover at H,
  cases H with Vi HVi,
  cases HVi with HVi HP,
  cases HVi with i Hi,
  existsi φ ⁻¹' Vi,
  existsi _, -- sorry Mario
    exact HP,
  existsi i,
  rw Hi,
  exact Zariski.induced.preimage_D _ _,
end
)

local attribute [instance] classical.prop_decidable

/-
open finset 
open presheaf_of_types_on_basis 
theorem application_of_tag00EJ {R : Type u} [comm_ring R] (r : R) {γ : Type u} {H : fintype γ}
  (f : γ → R) (Hcover : (1 : away r) ∈ span (↑(univ.image (of_comm_ring R (powers r) ∘ f)) : set (loc R (powers r)))) :
  let FPTB := (zariski.structure_presheaf_of_types_on_basis_of_standard R) in 
  
  
  (si : Π (i : γ), (zariski.structure_presheaf_of_types_on_basis_of_standard R).F ⟨f i,rfl⟩)
  (Hglue : ∀ i j : γ, res ⟨f i, rfl⟩ (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_left _ _) (si i) = 
              FPTB.res (BUi j) (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_right _ _) (si j))
  → ∃! s : FPTB.F BU, ∀ i : γ, FPTB.res BU (BUi i) (Hcover ▸ (set.subset_Union Ui i)) s = si i 


-/

-- Now let's try and prove the sheaf axiom for finite covers.

instance alpha_is_add_group_hom {R : Type u} {γ : Type u} [comm_ring R] [fintype γ] (f : γ → R) :
is_add_group_hom (tag00EJ.α f) :=
begin
  constructor,
  intros a b,
  funext,
  unfold tag00EJ.α,
  have H := localization.of_comm_ring_is_ring_hom R (powers (f i)),
  apply H.map_add,
end 

instance beta_is_add_group_hom {R : Type u} {γ : Type u} [comm_ring R] [fintype γ] (f : γ → R) :
is_add_group_hom (@tag00EJ.β R γ _ _ f) := begin
--unfold is_add_group_hom,
constructor,
intros a b,
funext,
show _ = (tag00EJ.β a j k) + (tag00EJ.β b j k),
unfold tag00EJ.β,
have H1 : localize_more_left (f j) (f k) ((a * b) j) = localize_more_left (f j) (f k) (a j)
+ localize_more_left (f j) (f k) (b j) := is_add_group_hom.add _ (a j) (b j),
rw H1,
have H2 : localize_more_right (f j) (f k) ((a * b) k) = localize_more_right (f j) (f k) (a k)
+ localize_more_right (f j) (f k) (b k) := is_add_group_hom.add _ (a k) (b k),
rw H2,
simp,
end 


--set_option pp.proofs true
set_option class.instance_max_depth 100
-- THIS IS BEING MOVED TO CANONICAL_ISOMORPHISM_NONSENSE
-- THIS PROOF IS LONG AND CURRENTLY UNFINISHED
theorem zariski.sheaf_of_types_on_standard_basis_for_finite_covers (R : Type u) [comm_ring R] :
  ∀ (U : set (X R)) (BU : U ∈ (standard_basis R)) (γ : Type u) (Fγ : fintype γ)
  (Ui : γ → set (X R)) (BUi :  ∀ i : γ, (Ui i) ∈ (standard_basis R))
  (Hcover: (⋃ (i : γ), (Ui i)) = U),
  sheaf_property_for_standard_basis (D_f_form_basis R) (zariski.structure_presheaf_of_types_on_basis_of_standard R)
   (λ U V ⟨f,Hf⟩ ⟨g,Hg⟩,⟨f*g,Hf.symm ▸ Hg.symm ▸ (tag00E0.lemma15 _ f g).symm⟩) U BU γ Ui BUi Hcover :=
begin
  intros U BU γ Hfγ Ui BUi Hcover si Hglue,
  -- from all this data our job is to find a global section
  cases BU with r Hr,
  let Rr := away r, -- our job is to find an element of Rr
  -- will get this from lemma_standard_covering₂
  let f0 : γ → R := λ i, (classical.some (BUi i)),
  let f : γ → Rr := λ i, of_comm_ring R (powers r) (classical.some (BUi i)),
  let f_proof := λ i, (classical.some_spec (BUi i) : Ui i = Spec.D' (f0 i)),
  -- need to check 1 ∈ span ↑(finset.image f finset.univ)
  -- to apply the algebra lemma for coverings.

  -- first let's check the geometric assertion
  have Hcoverr : (⋃ (i : γ), Spec.D' (f i)) = set.univ,
  { refine cover_of_cover_standard _ _,
    rw ←Hr,
    rw ←Hcover,
    congr,
    apply funext,
    intro i,
    rw ←(f_proof i) },

  -- now let's deduce that the ideal of Rr gen by im f is all of Rr
  let F : set Rr := set.range f,
  have H2 : ⋃₀ (Spec.D' '' (set.range f)) = set.univ,
    rw [←Hcoverr,←set.image_univ,←set.image_comp],
    simp [set.Union_eq_sUnion_image],
  rw [tag00E0.lemma16] at H2,
  have H3 : Spec.V (set.range f) = ∅,
    rw [←set.compl_univ,←H2,set.compl_compl],
  rw ←tag00E0.lemma05 at H3,
  have H1 : is_submodule (span (set.range f)) := by apply_instance,
  have H1' : is_ideal (span (set.range f)) := {..H1},
  letI := H1',
  have H4 : span (set.range f) = set.univ := (tag00E0.lemma08 Rr _).1 H3,
  clear F H2 H3 H1,
  have H5 : set.range f = ↑(finset.image f finset.univ),
    apply set.ext,intro x,split;intro H2,
    cases H2 with i Hi,rw ←Hi,simp,existsi i,refl,
    have : ∃ (a : γ), f a = x := by simpa using H2, exact this,
  rw H5 at H4,
  have H2 : (1 : Rr) ∈ span ↑(finset.image f finset.univ),
    rw H4,trivial,
  clear H5 H4,

  -- H2 is one of the inputs to Chris' lemma.

  -- What we seem to need now is a proof that if V is a standard open and V ⊆ U,
  -- then R[1/S(V)] = R[1/r][1/f] for V = D(f), and the unique R-algebra hom is an isom.

  -- so let's prove this.


-- s_proof no longer needed: we have canonical_iso.

  -- next thing we need is (s : Π (i : γ), loc Rr (powers (f i))) .
  -- But before we do that, let's define a function which sends i to a proof
  -- that if Ui = D(f i) and fi = image of f i in R[1/r] then O_X(Ui) = R[1/r][1/fi]
  -- Note that this is data -- the "=" is a given isomorphism between two totally different types
  /-
  let s_proof := λ i, begin
    let sival := (zariski.structure_presheaf_of_types_on_basis_of_standard R).F (BUi i),
    let fi := classical.some (BUi i),
    have Hfi_proof : Ui i = Spec.D' (fi) := classical.some_spec (BUi i),
    -- α = R[1/r][1/fi] -- ring Chris proved something about 
    -- β = R[1/fi] -- intermediate object
    -- γ = R[1/S(U)] -- definition of sheaf
    let sα : R → loc (away r) (powers (of_comm_ring R (powers r) fi)) :=
      of_comm_ring (away r) (powers (of_comm_ring R (powers r) fi)) ∘ of_comm_ring R (powers r),
    let sβ : R → loc R (powers fi) := of_comm_ring R (powers fi),  
    let sγ := (of_comm_ring R (non_zero_on_U (Spec.D' fi))),
    let Hi : R_alg_equiv sγ sβ := zariski.structure_presheaf_on_standard_is_loc fi,
    -- rw ←Hfi_proof at Hi -- fails,
    -- exact Hi.to_fun (si i), -- this is *supposed* to fail -- I need R[1/f][1/g] = R[1/g] here
    -- loc R (powers fi) = loc Rr (powers (f i))
    -- recall Rr is R[1/r] and U = D(r). We have D(fi) in U so "fi = g and r = f"
    -- so D(fi) is a subset of D(U)
    have Hsub : Spec.D' fi ⊆ Spec.D' r,
      rw [←Hfi_proof,←Hr,←Hcover],
      exact set.subset_Union Ui i,
    let Hloc : R_alg_equiv sα sβ := localization.loc_loc_is_loc Hsub, 
    -- now use symmetry and transitivity to deduce sα = sγ 
    let Hαγ : R_alg_equiv sγ sα := R_alg_equiv.trans Hi (R_alg_equiv.symm Hloc),
    exact Hαγ,
  end,
-/

  -- now in a position to apply lemma_standard_covering₂
  have Hexact1 := lemma_standard_covering₁ H2,
  have Hexact2 := lemma_standard_covering₂ f H2,
  
  -- At this point we have Hexact1 and Hexact2, which together are the assertion that
  -- if Rr = R[1/r] (with U=D(r)) and f : gamma -> Rr gives us a cover of U by U_i=D(f i)
  -- then the comm algebra sequence 00EJ is exact.

  -- We want to deduce an analogous statement for the global sections of O_X
  -- defined as O_X(U) = R[1/S(U)] and O_X(U_i) = R[1/S(U_i)].
  -- We have s_proof i : R_alg_equiv (R->R[1/S(U_i)]) (R->R[1/r]->R[1/r][1/f_i])
  -- We will surely need R_alg_equiv (R->R[1/S(U)]) (R->R[1/r]) but we will have
  -- this somewhere : it will be zariski.structure_presheaf_on_standard_is_loc blah
  have HUbasic := zariski.structure_presheaf_on_standard_is_loc r,

  -- goal currently
  --∃! (s : (zariski.structure_presheaf_of_types_on_basis_of_standard R).F _),
  --  ∀ (i : γ), (zariski.structure_presheaf_of_types_on_basis_of_standard R).res _ _ _ s = si i

  -- This is the point where I want to say "done because everything is canonical".
  -- 
  -- A = Rr
  -- B = prod_i Rr[1/f i]
  -- C = prod_{j,k} Rr[1/(f j) * (f k)] 
  -- A' = value of sheaf on U
  -- B' = prod_i values on D(f0 i)
  -- C' = prod j k values in D((f0 j) * (f0 k))

  have H4exact : ∀ (b : Π (i : γ), loc Rr (powers (f i))), tag00EJ.β b = 0 → (∃! (a : Rr), tag00EJ.α f a = b),
  { intros b Hb,
    cases ((Hexact2 b).1 Hb) with a Ha,
    existsi a,
    split,exact Ha,
    intros y Hy,
    apply Hexact1,
    rw Ha,
    rw Hy
  }, 

  have fa : R_alg_equiv 
              (of_comm_ring R (powers r)) 
              (of_comm_ring R (non_zero_on_U U)) := begin 
                rw Hr,
                exact (zariski.structure_presheaf_on_standard_is_loc r).symm,
              end, 

--  have : is_add_group_hom fa.to_equiv := sorry, --fa.to_is_ring_hom.map_add,

  have fbi : ∀ i : γ, R_alg_equiv
               ((of_comm_ring Rr (powers (f i))) ∘ (of_comm_ring R (powers r)))
               (of_comm_ring R (non_zero_on_U (Ui i))) := begin
                 intro i,
                 rw f_proof i,
                 have H : Spec.D' (f0 i) ⊆ Spec.D' r,
                 { rw ←Hr,
                   rw ←(f_proof i),
                   rw ←Hcover,
                   apply set.subset_Union Ui i,
                 },
      exact (canonical_iso H).symm,

  end,

  have fcjk : ∀ j k : γ, R_alg_equiv 
                ((of_comm_ring Rr (powers (f j * f k))) ∘ (of_comm_ring R (powers r)))
                (of_comm_ring R (non_zero_on_U (Ui j ∩ Ui k))) := begin
                  intros j k,
                  rw f_proof j,
                  rw f_proof k,
                  rw ←tag00E0.lemma15,
                  have H : f j * f k = of_comm_ring R (powers r) (f0 j * f0 k),
                    rw (localization.of_comm_ring_is_ring_hom R (powers r)).map_mul,
                  rw H,
                  have H' : Spec.D' (f0 j * f0 k) ⊆ Spec.D' r,
                  { rw tag00E0.lemma15,
                    apply set.subset.trans 
                      (set.inter_subset_left (Spec.D' (f0 j)) (Spec.D' (f0 k))) (_ :
                      (Spec.D' (f0 j)) ⊆ Spec.D' r),
                    rw ←Hr,
                    rw ←(f_proof j),
                    rw ←Hcover,
                    apply set.subset_Union Ui j,
                  },
                  -- now rewrite Uj ∩ Uk as D(f0j * f0k)
                  -- and there might be an issue that f j * f k isn't
                  -- defeq to the image of f0 j * f0 k
                  -- Once these are fixed the below might work.
                  exact (canonical_iso H').symm,
                end,

  let H3 : ∀ (i : γ), loc Rr (powers (f i)) ≃ loc R (non_zero_on_U (Ui i)),
    intro i,exact (fbi i).to_equiv,
  let H3' : (Π (i : γ), loc Rr (powers (f i))) ≃ Π (i : γ), loc R (non_zero_on_U (Ui i)) := equiv.Pi_congr_right H3,

  let H4 : ∀ (j k : γ), loc Rr (powers (f j * f k)) ≃ loc R (non_zero_on_U (Ui j ∩ Ui k)),
    intros j k, exact (fcjk j k).to_equiv,

  let H4' : ∀ j, (Π k, loc Rr (powers (f j * f k))) ≃ (Π k, loc R (non_zero_on_U (Ui j ∩ Ui k))),
    intro j, exact equiv.Pi_congr_right (H4 j),
  
  let H4'' : (Π (j k : γ), loc Rr (powers (f j * f k))) ≃ Π (j k : γ),loc R (non_zero_on_U (Ui j ∩ Ui k)),
    exact equiv.Pi_congr_right H4',

  have H4g : ∀ j k, is_add_group_hom (H4 j k) := by apply_instance,
  have H4g' : ∀ j, is_add_group_hom (H4' j) := by apply_instance,

--  have H4 : ∀ j k : γ, loc Rr (powers (f j * f k)) ≃ loc R (non_zero_on_U (Ui j ∩ Ui k)),
--    intros j k, exact (fcjk j k).to_equiv,

  have Hcanonical := fourexact_from_iso_to_fourexact 
   (tag00EJ.α f : Rr → (Π (i : γ), away (f i)))
   (tag00EJ.β) 
   (H4exact) --H4exact
   (fa.to_equiv) -- fa
--   (equiv.prod H3 : (Π (i : γ), loc Rr (powers (f i))) ≃ Π (i : γ), loc R (non_zero_on_U (Ui i))) -- fb
--   (H3' : (Π (i : γ), loc Rr (powers (f i))) ≃ Π (i : γ), loc R (non_zero_on_U (Ui i))) -- fb
--   H3'
--   (H3' : ((Π (i : γ), loc Rr (powers (f i))) ≃ (Π (i : γ), loc R (non_zero_on_U (Ui i))))) -- fb
--   (by exact H3')
   (_ : ((Π (i : γ), loc Rr (powers (f i))) ≃ (Π (i : γ), loc R (non_zero_on_U (Ui i))))) -- fb
   (_ : (Π (j k : γ), loc Rr (powers (f j * f k))) ≃ Π (j k : γ),loc R (non_zero_on_U (Ui j ∩ Ui k))) -- fa : A ≃ A', fb fc
    _ -- ab' -- map
    _ -- bc' -- map 
    _ _, -- H1 H2 -- diags commute

    -- modulo the ten extra goals which just appeared, we're nearly done!
  show (Π (i : γ), loc Rr (powers (f i))) ≃ Π (i : γ), loc R (non_zero_on_U (Ui i)),
    exact H3',  
  show (Π (j k : γ), loc Rr (powers (f j * f k))) ≃ Π (j k : γ),loc R (non_zero_on_U (Ui j ∩ Ui k)),
    exact H4'',

  show is_add_group_hom H3',
    exact is_add_group_hom.Pi_lift (λ i, fbi i),

--  let H4'' : (Π (j k : γ), loc Rr (powers (f j * f k))) ≃ Π (j k : γ),loc R (non_zero_on_U (Ui j ∩ Ui k)),
 --   have H4'' (j : γ) : is_group_hom (Π (k : γ),   
 --   exact is_add_group_hom.Pi_lift (λ j, _),--is_add_group_hom.Pi_lift (λ k,_)),
  show is_add_group_hom ⇑H4'',
  { have H4unravel : 
      (H4'' : (Π (j k : γ), loc Rr (powers (f j * f k))) → Π (j k : γ),loc R (non_zero_on_U (Ui j ∩ Ui k)))
           = (λ Fjk j k, fcjk j k (Fjk j k)),
      refl,
    show is_add_group_hom (λ Fjk j k, fcjk j k (Fjk j k) : (Π (j k : γ), loc Rr (powers (f j * f k))) → Π (j k : γ),loc R (non_zero_on_U (Ui j ∩ Ui k))),
    sorry    
--    suffices : ∀ j, is_add_group_hom (
--      λ Fk k, fcjk j k (Fk k) : (Π k,loc Rr (powers (f j * f k))) → Π (k : γ),loc R (non_zero_on_U (Ui j ∩ Ui k))),
--      exact is_add_group_hom.Pi_lift (∀ j, (λ Fk k, fcjk j k (Fk k))),
  },
      -- : (Π k,loc Rr (powers (f j * f k))) → Π (k : γ),loc R (non_zero_on_U (Ui j ∩ Ui k)))),
        

repeat {sorry},
end 
#print ring_equiv
#check equiv.Pi_congr_right

#check @fourexact_from_iso_to_fourexact


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
  Π (f : ?M_1), R_alg_equiv (of_comm_ring ?M_1 (non_zero_on_U (Spec.D' f))) (of_comm_ring ?M_1 (powers f))
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





/-
-- below was initial attempt to formulate stuff

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
-/