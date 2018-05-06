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
universes u v w uu

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

-- KB failed to get this to work

--theorem XXX {α β : Type} : has_coe_to_fun (equiv α β) := by apply_instance

--instance R_alg_equiv_coe_to_fun {R : Type u} {α : Type v} {β : Type w} [comm_ring R] [comm_ring α] [comm_ring β]
--  (sα : R → α) (sβ : R → β) : has_coe_to_fun (R_alg_equiv sα sβ) := λ C,(C.to_equiv)

lemma R_alg_equiv.symm {R : Type u} {α : Type v} {β : Type w} 
  [comm_ring R] [comm_ring α] [comm_ring β]
  {sα : R → α} {sβ : R → β} :
  R_alg_equiv sα sβ → R_alg_equiv sβ sα :=
  λ H, { R_alg_hom := begin
         let f := H.to_fun,
         have H2 : sβ = f ∘ sα := H.R_alg_hom,
         let g := H.inv_fun,
         show sα = g ∘ sβ,
         rw H2,
         funext,
         show _ = g (f (sα x)),
         conv begin
           to_lhs,
           rw ←H.left_inv (sα x),
         end,
       end,
    ..(H.to_ring_equiv).symm
  }

lemma R_alg_equiv.trans {R : Type u} {α : Type v} {β : Type w} {γ : Type uu}
  [comm_ring R] [comm_ring α] [comm_ring β] [comm_ring γ]
  {sα : R → α} {sβ : R → β} {sγ : R → γ} :
  R_alg_equiv sα sβ → R_alg_equiv sβ sγ → R_alg_equiv sα sγ :=
λ H1 H2,
{ R_alg_hom := begin
     show sγ = H2.to_fun ∘ (H1.to_fun ∘ sα),
     funext,
     have H3 : sγ = H2.to_fun ∘ sβ := H2.R_alg_hom,
     have H4 : sβ = H1.to_fun ∘ sα := H1.R_alg_hom,
     conv begin
       to_lhs,
       rw H3,
       change H2.to_fun (sβ x),
     end,
     conv in (sβ x) begin
       rw H4,
     end,
  end,
  ..(ring_equiv.trans H1.to_ring_equiv H2.to_ring_equiv)
}

open localization -- should have done this ages ago

-- TODO -- I don't need those two maps to be id! id is clearly an R-alg com so use uniqueness!!
definition R_alg_equiv_of_unique_homs {R : Type u} {α : Type v} {β : Type w} [comm_ring R] [comm_ring α] [comm_ring β]
  {sα : R → α} {sβ : R → β} {f : α → β} {g : β → α} {hα : α → α} {hβ : β → β}
  [is_ring_hom sα] [is_ring_hom sβ] [H : is_ring_hom f] [is_ring_hom g] [is_ring_hom hα] [is_ring_hom hβ] : 
is_unique_R_alg_hom sα sβ f → is_unique_R_alg_hom sβ sα g → is_unique_R_alg_hom sα sα hα → is_unique_R_alg_hom sβ sβ hβ
  → R_alg_equiv sα sβ := λ Hαβ Hβα Hαα Hββ,
{ to_fun := f,
  inv_fun := g,
  left_inv := λ x, begin
    have Hα : id = hα,
      exact Hαα.is_unique id rfl,
    show (g ∘ f) x = x,
    rw [comp_unique sα sβ sα f g hα Hαβ Hβα Hαα,←Hα],
    refl
  end,
  right_inv := λ x, begin
    have Hβ : id = hβ,
      exact Hββ.is_unique id rfl,
    show (f ∘ g) x = x,
    rw [comp_unique sβ sα sβ g f hβ Hβα Hαβ Hββ,←Hβ],
    refl
  end,  
  is_ring_hom := H,
  R_alg_hom := show sβ = f ∘ sα, from Hαβ.R_alg_hom
}

-- This proof could be simpler: a lot of the definitions would follow from
-- universal properties, but Kenny just proved them directly anyway.
-- It's the proof that if U=D(f) and S=S(U) is the functions which are non-vanishing
-- on U then R[1/S]=R[1/f] as R-algebras.
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

-- we now begin to check the sheaf axiom for a finite covers by basis elements.

-- To get Chris' lemma to apply to covers of D(f) (rather than a cover of R)
-- we need R[1/f][1/g] = R[1/g] if D(g) ⊆ D(f), so let's prove this from the
-- universal property.

-- warm-up:
-- f invertible in R implies R[1/f] uniquely R-iso to R
noncomputable definition localization.loc_unit {R : Type u} [comm_ring R] (f : R) (H : is_unit f) : 
R_alg_equiv (id : R → R) (of_comm_ring R (powers f)) := 
R_alg_equiv_of_unique_homs 
  (unique_R_alg_from_R (of_comm_ring R (powers f)))
  (away_universal_property f id H)
  (unique_R_alg_from_R id)
  (id_unique_R_alg_from_loc _) 

set_option class.instance_max_depth 52 -- !!
--set_option trace.class_instances true
/-- universal property of inverting one element and then another -/
theorem away_away_universal_property {R : Type u} [comm_ring R] (f : R)
(g : loc R (powers f)) {γ : Type v} [comm_ring γ] (sγ : R → γ) [is_ring_hom sγ] (Hf : is_unit (sγ f))
(Hg : is_unit (away.extend_map_of_im_unit sγ Hf g)) :
is_unique_R_alg_hom 
  ((of_comm_ring (away f) (powers g)) ∘ (of_comm_ring R (powers f))) 
  sγ
  (away.extend_map_of_im_unit (away.extend_map_of_im_unit sγ Hf) Hg) := 
begin
  let α := loc R (powers f),
  let β := loc α (powers g),
  let sα := of_comm_ring R (powers f),
  let fαβ := of_comm_ring α (powers g),
  let sβ := fαβ ∘ sα,
  let fαγ := away.extend_map_of_im_unit sγ Hf,
  let fβγ := away.extend_map_of_im_unit fαγ Hg,
  have HUαγ : is_unique_R_alg_hom sα sγ fαγ := away_universal_property f sγ Hf,
  have HUβγ : is_unique_R_alg_hom fαβ fαγ fβγ := away_universal_property g fαγ Hg,
  have Hαγ : sγ = fαγ ∘ sα := HUαγ.R_alg_hom,
  have Hβγ : fαγ = fβγ ∘ fαβ := HUβγ.R_alg_hom,
  have Htemp : is_unique_R_alg_hom sα sγ fαγ ↔ is_unique_R_alg_hom sα (fβγ ∘ fαβ ∘ sα) (fβγ ∘ fαβ),
    simp [Hαγ,Hβγ],
  have Htemp2 : is_unique_R_alg_hom fαβ fαγ fβγ ↔ is_unique_R_alg_hom fαβ (fβγ ∘ fαβ) fβγ,
    simp [Hβγ],
  have H : is_unique_R_alg_hom (fαβ ∘ sα) (fβγ ∘ fαβ ∘ sα) fβγ := unique_R_of_unique_R_of_unique_Rloc sα fαβ fβγ (Htemp.1 HUαγ) (Htemp2.1 HUβγ),
  have Htemp3 : is_unique_R_alg_hom (fαβ ∘ sα) (fβγ ∘ fαβ ∘ sα) fβγ ↔ is_unique_R_alg_hom (fαβ ∘ sα) sγ fβγ,
    simp [Hαγ,Hβγ],
  exact Htemp3.1 H
end 

/-- universal property of inverting two elements of R one by one -/
theorem away_away_universal_property' {R : Type u} [comm_ring R] (f g : R)
{γ : Type v} [comm_ring γ] (sγ : R → γ) [is_ring_hom sγ] (Hf : is_unit (sγ f))
(Hg : is_unit (sγ g)) :
is_unique_R_alg_hom
  ((of_comm_ring (away f) (powers (of_comm_ring R (powers f) g))) ∘ (of_comm_ring R (powers f))) 
  sγ
  (away.extend_map_of_im_unit (away.extend_map_of_im_unit sγ Hf) (begin rwa away.extend_map_extends end)) :=
away_away_universal_property f (of_comm_ring R (powers f) g) sγ Hf (begin rwa away.extend_map_extends end)

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

set_option class.instance_max_depth 93
-- I don't use the next theorem, it was just a test for whether I had the right universal properties.
noncomputable definition loc_is_loc_loc {R : Type u} [comm_ring R] (f g : R) :
R_alg_equiv 
  ((of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)))
  ∘ (of_comm_ring R (powers f)))
  (of_comm_ring R (powers (f * g))) :=
R_alg_equiv_of_unique_homs
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

-- here is what we need to evaluate the sheaf 
noncomputable definition localization.loc_loc_is_loc {R : Type u} [comm_ring R] {f g : R} (H : Spec.D' g ⊆ Spec.D' f) :
  let sα := (of_comm_ring (away f) (powers (of_comm_ring R (powers f) g))) ∘ (of_comm_ring R (powers f)) in
  let sβ := of_comm_ring R (powers g) in
R_alg_equiv sα sβ := 
begin
  have Htemp : is_ring_hom (of_comm_ring (away f) (powers (of_comm_ring R (powers f) g))) := by apply_instance,
  letI := Htemp,
  let sα : R → loc (away f) (powers (of_comm_ring R (powers f) g)) := 
    (of_comm_ring (away f) (powers (of_comm_ring R (powers f) g))) ∘ (of_comm_ring R (powers f)),
  let sβ := of_comm_ring R (powers g),
  have HUfα : is_unit (sα f),
    show is_unit ((of_comm_ring (away f) (powers (of_comm_ring R (powers f) g))) ((of_comm_ring R (powers f)) f)),
    exact im_unit_of_unit (of_comm_ring (away f) (powers (of_comm_ring R (powers f) g))) (unit_of_in_S (away.in_powers f)),
  have HUfβ : is_unit (sβ f) := lemma_standard_open_1a R f g H,
  have HUgα : is_unit (sα g) := unit_of_in_S (away.in_powers (of_comm_ring R (powers f) g)),
  have HUgβ : is_unit (sβ g) := unit_of_in_S (away.in_powers g),
  exact R_alg_equiv_of_unique_homs 
    (away_away_universal_property' f g sβ HUfβ HUgβ)
    (away_universal_property g sα HUgα : is_unique_R_alg_hom sβ sα _)
    (away_away_universal_property' f g sα HUfα HUgα)
    (away_universal_property g sβ HUgβ)
end

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

-- Now I need the following technical result:
-- If V = D(g) in U = D(f) in Spec(R)
-- then structure sheaf evaluated on V (R[1/S(V)]) is R-isomorphic to R[1/f][1/gbar]
-- with gbar = image of g. The proof goes via R[1/g]
-- It is also true that the R-isomorphism is the unique R-homomorphism
-- between these rings -- see the lemma after this.
noncomputable definition canonical_iso {R : Type u} [comm_ring R] {f g : R} (H : Spec.D' g ⊆ Spec.D' f) :
let gbar := of_comm_ring R (powers f) g in
let sα : R → loc (away f) (powers gbar) :=
  of_comm_ring (away f) (powers gbar) ∘ of_comm_ring R (powers f) in
let sγ := (of_comm_ring R (non_zero_on_U (Spec.D' g))) in
R_alg_equiv sγ sα :=
R_alg_equiv.trans
  (zariski.structure_presheaf_on_standard_is_loc g )
  (R_alg_equiv.symm (localization.loc_loc_is_loc H))

#check id

-- and we also need that the canonical iso is the unique R-alg hom
-- NB Chris suggests I remove the first three let's.
theorem canonical_iso_is_canonical_hom {R : Type u} [comm_ring R] {f g : R} (H : Spec.D' g ⊆ Spec.D' f) :
let gbar := of_comm_ring R (powers f) g in
let sα : R → loc (away f) (powers gbar) :=
  of_comm_ring (away f) (powers gbar) ∘ of_comm_ring R (powers f) in
let sγ := (of_comm_ring R (non_zero_on_U (Spec.D' g))) in
let H3 : is_ring_hom sα := by apply_instance in
let H2 := (canonical_iso H).is_ring_hom in
let H4 : is_ring_hom sγ := by apply_instance in
@is_unique_R_alg_hom _ _ _ _ _ _ sγ sα (canonical_iso H).to_fun H4 H3 H2 := 
begin
letI := (canonical_iso H).is_ring_hom,
have H5 := unique_R_alg_from_loc (canonical_iso H).to_fun,
have H6 := (canonical_iso H).R_alg_hom.symm,
simp [H6] at H5,
exact H5,
end 

-- is_unique_R_alg_hom sγ sα (canonical_hom H) := sorry

local attribute [instance] classical.prop_decidable

-- Now let's try and prove the sheaf axiom for finite covers.
--set_option pp.proofs true
theorem zariski.sheaf_of_types_on_standard_basis_for_finite_covers (R : Type u) [comm_ring R] :
  ∀ (U : set (X R)) (BU : U ∈ (standard_basis R)) (γ : Type u) (Fγ : fintype γ)
  (Ui : γ → set (X R)) (BUi :  ∀ i : γ, (Ui i) ∈ (standard_basis R))
  (Hcover: (⋃ (i : γ), (Ui i)) = U),
  sheaf_property (D_f_form_basis R) (zariski.structure_presheaf_of_types_on_basis_of_standard R)
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


  -- next thing we need is (s : Π (i : γ), loc Rr (powers (f i))) .
  -- But before we do that, let's define a function which sends i to a proof
  -- that if Ui = D(f i) and fi = image of f i in R[1/r] then O_X(Ui) = R[1/r][1/fi]
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

  -- now in a position to apply lemma_standard_covering₂
  have H3 := lemma_standard_covering₂ f H2,
  repeat {admit},
end 

#print R_alg_equiv
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