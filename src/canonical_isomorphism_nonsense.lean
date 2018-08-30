/- This file contains the construction of the presheaf of rings on Spec(R) and the proof
   that it satisfies the sheaf axiom for finite covers by basic open sets.

   We seem to need to explicitly tell Lean that something canonically isomorphic
   to an exact sequence is an exact sequence.

   We start with Kenny's non-canonical proof that something iso to a three term exact seq is exact.

   We then use my ghastly application coming from localization.

   This file corresponds to the line in tag01HR:
   "Thus we may apply Algebra, Lemma 10.22.2 to the module Mf over Rf and the elements g1,…,gn. 
   We conclude that the sequence is exact."
   The issue is that there are a lot of diagrams which commute, but this needs checking.

-/
import algebra.group data.set data.equiv.basic -- for comm diag stuff
import tag00DY -- definition of standard basis on Spec(R) plus proof it's a basis
import tag00E0
import tag00EJ -- finite cover by basic opens sheaf axiom
import tag009I -- definition of presheaf of types on basis
import tag009L -- definition of basis_is_compact 
--import group_theory.submonoid  
import ring_theory.localization 
import Kenny_comm_alg.Zariski 
--import tag00E0 
import tag01HS -- for "lemma_standard_open" giving map R[1/f] -> R[1/g] from D(g) ⊆ D(f) 
--import tag009I -- presheaf of types on a basis
--import tag00DY -- claim that D(f) form a basis
--import tag006N -- presheaves / sheaves of rings on a basis
--import tag009P -- presheaf of rings on a basis
--import tag009L -- sheaf for finite covers on basis -> sheaf for basis
import tag00EJ 
import linear_algebra -- for span 

local attribute [instance] classical.prop_decidable

universes u0 u v w

definition Pi_lift_map₁ {γ : Type u} {F : γ → Type u} {G : γ → Type u} 
  (H : ∀ i : γ, F i → G i) : (Π i, F i) → Π i, G i := λ Fi i, H i (Fi i)

definition Pi_lift_map₂ {γ : Type u} {X : Type u} {G : γ → Type u} 
  (H : ∀ i : γ, X → G i) : X → Π i, G i := λ x i, H i x

namespace is_add_group_hom

variables {α : Type*} {β : Type*} [add_group α] [add_group β] (f : α → β) [hf : is_add_group_hom f]

instance ring_hom_is_add_group_hom {α β : Type u} [ring α] [ring β] (f : α → β) [is_ring_hom f] : is_add_group_hom f :=
⟨λ _ _, is_ring_hom.map_add f⟩

def ker : set α :=
{ x | f x = 0 }

instance Pi_lift {γ : Type u} {F : γ → Type u} {G : γ → Type u} [∀ i, add_group (F i)]
[∀ i, add_group (G i)] (H : ∀ i : γ, F i → G i) [∀ i, is_add_group_hom (H i)] :
 is_add_group_hom (Pi_lift_map₁ H) := ⟨λ a b, funext $ λ i,
show H i ((a i) + (b i)) = H i (a i) + H i (b i),
by rw (add (H i))⟩

instance equiv.Pi_congr_right {γ : Type u} {F : γ → Type u} {G : γ → Type u} [∀ i, add_group (F i)]
[∀ i, add_group (G i)] (H : ∀ i : γ, F i ≃ G i) [∀ i, is_add_group_hom (H i)] :
 is_add_group_hom (equiv.Pi_congr_right H) := 
-- is_add_group_hom.Pi_lift H
 is_add_group_hom.Pi_lift (λ i, H i)

end is_add_group_hom

namespace equiv

theorem to_fun.injective {α β : Type u} (e : α ≃ β) : function.injective e := 
function.injective_of_has_left_inverse ⟨e.symm,e.inverse_apply_apply⟩

end equiv

--class is_alg_hom (R : Type u) [ring R] {A B : Type u} [ring A] [ring B] (sA : R → A) (sB : R → B)
--[is_ring_hom sA] [is_ring_hom sB] (f : A → B) extends is_ring_hom f : Prop :=
--(commutes : ∀ r, f (sA r) = sB r)

namespace is_ring_hom

instance Pi_lift_map₁ {γ : Type u} {F : γ → Type u} {G : γ → Type u} [∀ i, ring (F i)]
[∀ i, ring (G i)] (H : ∀ i : γ, F i → G i) [H' : ∀ i, is_ring_hom (H i)] :
 is_ring_hom (Pi_lift_map₁ H) := 
{ map_add := λ a b, funext $ λ x,begin 
    show H x (a x + b x) = H x (a x) + H x (b x), 
    rw (H' x).map_add,
    end,
  map_mul := λ a b, funext $ λ x,begin 
    show H x (a x * b x) = H x (a x) * H x (b x), 
    rw (H' x).map_mul,
    end,
  map_one := funext $ λ x,begin 
    show H x 1 = 1,
    exact (H' x).map_one
  end
}

instance equiv.Pi_congr_right {γ : Type u} {F : γ → Type u} {G : γ → Type u} [∀ i, ring (F i)]
[∀ i, ring (G i)] (H : ∀ i : γ, F i ≃ G i) [H' : ∀ i, is_ring_hom (H i)] :
 is_ring_hom (equiv.Pi_congr_right H) := is_ring_hom.Pi_lift_map₁ (λ i, H i)

end is_ring_hom 

-- If A -> B -> C is isomorphic to A' -> B' -> C' and first sequence is exact then second is.
-- But I don't ever use this now.
/-
theorem three (A B C A' B' C' : Type*)
  [add_comm_group A] [add_comm_group A']
  [add_comm_group B] [add_comm_group B']
  [add_comm_group C] [add_comm_group C']
  (ab : A → B) [is_add_group_hom ab]
  (bc : B → C) [is_add_group_hom bc]
  (Habc : set.range ab = is_add_group_hom.ker bc)
  (fa : A ≃ A') [is_add_group_hom fa]
  (fb : B ≃ B') [is_add_group_hom fb]
  (fc : C ≃ C') [is_add_group_hom fc]

  (ab' : A' → B') [is_add_group_hom ab']
  (bc' : B' → C') [is_add_group_hom bc']
  (H1 : fb ∘ ab = ab' ∘ fa)
  (H2 : fc ∘ bc = bc' ∘ fb) :

  set.range ab' = is_add_group_hom.ker bc' :=
begin
  apply set.ext,
  intro b',
  split,
  { intro hb',
    cases hb' with a' ha',
    simp [is_add_group_hom.ker],
    let a := fa.symm a',
    have ha : fa a = a',
    { simp [a] },
    rw [← ha', ← ha],
    change bc' ((ab' ∘ fa) a) = 0,
    rw ← H1,
    change (bc' ∘ fb) (ab a) = 0,
    rw ← H2,
    have H3 : ab a ∈ is_add_group_hom.ker bc,
    { rw ← Habc, existsi a, simp },
    simp [is_add_group_hom.ker] at H3 ⊢,
    rw H3,
    apply is_add_group_hom.zero },
  { intro hb',
    let b := fb.symm b',
    have hb : fb b = b',
    { simp [b] },
    simp [is_add_group_hom.ker] at hb',
    rw ← hb at hb',
    change (bc' ∘ fb) b = 0 at hb',
    rw ← H2 at hb',
    rw ← is_add_group_hom.zero fc at hb',
    replace hb' := congr_arg fc.symm hb',
    simp at hb',
    have H3 : b ∈ set.range ab,
    { rwa Habc },
    cases H3 with a ha,
    existsi fa a,
    change (ab' ∘ fa) a = b',
    rw ← H1,
    simp [ha] }
end

-- Thanks Kenny.
-/


-- Now start moving stuff from tag01HR.lean which has got really
-- unwieldy. Here I am going to prove the sheaf on a finite basis
-- statement from the ring theory lemma tag00EJ

-- First here's the choice-free definition of the structure presheaf

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

-- A key notion for us is that of a canonical R-algebra isomorphism.
-- Because I still don't quite understand what makes an isomorphism
-- canonical let's just start with the notion of an R-algebra isomorphism.

structure R_alg_equiv {R : Type u} {α : Type v} {β : Type w} [comm_ring R] [comm_ring α] [comm_ring β]
  (sα : R → α) (sβ : R → β) extends ring_equiv α β :=
(R_alg_hom : sβ = to_fun ∘ sα)

instance R_alg_equiv_coe_to_fun {R : Type u} {α : Type v} {β : Type w} [comm_ring R] [comm_ring α] [comm_ring β]
  (sα : R → α) (sβ : R → β) : has_coe_to_fun (R_alg_equiv sα sβ) := ⟨_,λ h,h.to_fun⟩

instance R_alg_equiv_is_ring_hom {R : Type u} {α : Type v} {β : Type w} [comm_ring R] [comm_ring α] [comm_ring β]
  (sα : R → α) (sβ : R → β) (H : R_alg_equiv sα sβ) : is_ring_hom H := H.is_ring_hom 

namespace R_alg_equiv

lemma symm {R : Type u} {α : Type v} {β : Type w} 
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

/- we have his for ring_equiv and I've never implemented this version here
  lemma inv_fun_is_ring_hom {R : Type u} {α : Type v} {β : Type w} 
  [comm_ring R] [comm_ring α] [comm_ring β]
  {sα : R → α} {sβ : R → β} (H : R_alg_equiv sα sβ) : is_ring_hom H.inv_fun := sorry 
-/
lemma trans {R : Type u0} {α : Type u} {β : Type v} {γ : Type w}
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

-- TODO
-- I need to now give easy access to "inv_fun is ring hom".

open localization 

definition of_unique_homs {R : Type u} {α : Type v} {β : Type w} [comm_ring R] [comm_ring α] [comm_ring β]
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

end R_alg_equiv -- namespace


-- The proof below (is_loc) could be simpler: a lot of the definitions would follow from
-- universal properties, but Kenny just proved them directly anyway.
-- It's the proof that if U=D(f) and S=S(U) is the functions which are non-vanishing
-- on U then R[1/S]=R[1/f] as R-algebras.

open localization 

noncomputable definition zariski.structure_presheaf_on_standard_is_loc {R : Type u} [comm_ring R] (f : R) :
  R_alg_equiv (of_comm_ring R _ : R → zariski.structure_presheaf_on_standard (Spec.D'(f)) (⟨f,rfl⟩))
    (of_comm_ring R (powers f) : R → away f) :=  
{ to_fun      := extend_map_of_im_unit
    (of_comm_ring R (powers f))
    (λ s hs, lemma_standard_open_1a R _ _ hs),
  is_ring_hom := extend_map_of_im_unit.is_ring_hom _ _,
  inv_fun     := away.extend_map_of_im_unit
    (of_comm_ring R _)
    ⟨mk _ _ ⟨1, f, set.subset.refl _⟩,
     quotient.sound ⟨1, is_submonoid.one_mem _, by simp⟩⟩,
  left_inv    := @unique _ _ _ _ _ _ _ _ 
    (@@is_ring_hom.comp _ _ _
       (extend_map_of_im_unit.is_ring_hom _ _) _ _
       (extend_map_of_im_unit.is_ring_hom _ _))
    (ring_equiv.refl _).is_ring_hom
    (by intro x; dsimp [ring_equiv.refl, equiv.refl]; rw [extend_map_extends, extend_map_extends]),
  right_inv   := @localization.unique _ _ _ _ _ _ _ _
    (@@is_ring_hom.comp _ _ _
       (extend_map_of_im_unit.is_ring_hom _ _) _ _
       (extend_map_of_im_unit.is_ring_hom _ _))
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

-- we now need some universal properties coming from localization.

set_option class.instance_max_depth 52 -- !!

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
  -- it's the next line which needs class.instance_max_depth 52
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

-- To get Chris' lemma to apply to covers of D(f) (rather than a cover of R)
-- we need R[1/f][1/g] = R[1/g] if D(g) ⊆ D(f), so let's prove this from the
-- universal property.

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
  exact R_alg_equiv.of_unique_homs 
    (away_away_universal_property' f g sβ HUfβ HUgβ)
    (away_universal_property g sα HUgα : is_unique_R_alg_hom sβ sα _)
    (away_away_universal_property' f g sα HUfα HUgα)
    (away_universal_property g sβ HUgβ)
end

-- Now I need the following technical result:
-- If V = D(g) ⊆ U = D(f) in Spec(R)
-- then structure sheaf evaluated on V (R[1/S(V)]) is R-isomorphic to R[1/f][1/gbar]
-- with gbar = image of g. The map is from R[1/S(V)] to R[1/f][1/gbar]
-- The proof goes via R[1/g]
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

-- and we also need that the canonical iso is the unique R-alg hom.
-- From R[1/S(V)] to R[1/f][1/gbar] the result is here:

-- NB Chris suggests I remove the first three let's.
theorem canonical_iso_is_canonical_hom₁ {R : Type u} [comm_ring R] {f g : R} (H : Spec.D' g ⊆ Spec.D' f) :
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

-- now let's go the other way -- but do I need this?
/-
theorem canonical_iso_is_canonical_hom₂ {R : Type u} [comm_ring R] {f g : R} (H : Spec.D' g ⊆ Spec.D' f) :
let gbar := of_comm_ring R (powers f) g in
let sα : R → loc (away f) (powers gbar) :=
  of_comm_ring (away f) (powers gbar) ∘ of_comm_ring R (powers f) in
let sγ := (of_comm_ring R (non_zero_on_U (Spec.D' g))) in
let H3 : is_ring_hom sα := by apply_instance in
let H2 : is_ring_hom (canonical_iso H).inv_fun := ring_equiv.inv_fun_is_ring_hom (canonical_iso H).to_ring_equiv in
let H4 : is_ring_hom sγ := by apply_instance in
@is_unique_R_alg_hom _ _ _ _ _ _ sα sγ (canonical_iso H).inv_fun H3 H4 H2 := sorry
-/

-- Chris has proved that 0-> A -> sum A_{g_i} -> sum A_{g_i g_j} is exact
-- if Spec(A) is covered by D(g_i) (a finite cover).

-- I want to prove that if U = D(f) is open and covered by U_i = D(g_i)
-- and if A = R[1/S(U)] then
-- 0 -> A -> sum R[1/S(U_i)] -> sum R[1/S(U_i intersect U_j)] is exact

-- Let's formulate exactly what we need.

theorem fourexact_from_iso_to_fourexact {A B C A' B' C' : Type u}
  [add_comm_group A] [add_comm_group A']
  [add_comm_group B] [add_comm_group B']
  [add_comm_group C] [add_comm_group C']
  (ab : A → B) [is_add_group_hom ab]
  (bc : B → C) [is_add_group_hom bc]
--  (Habc : set.range ab = is_add_group_hom.ker bc)
  (H4exact : ∀ b : B, bc b = 0 → ∃! a : A, ab a = b)
  (fa : A ≃ A') [is_add_group_hom fa]
  (fb : B ≃ B') [is_add_group_hom fb]
  (fc : C ≃ C') [is_add_group_hom fc]

  (ab' : A' → B') [is_add_group_hom ab']
  (bc' : B' → C') [is_add_group_hom bc']
  (H1 : ∀ a, fb (ab a) = ab' (fa a))
  (H2 : ∀ b, fc (bc b) = bc' (fb b))
  : ∀ b' : B', (bc' b' = 0 → ∃! a' : A', ab' a' = b') := 
begin
  intros b' Hb',
  let b := fb.symm b',
    have H3 : fc (bc b) = 0,
    rw H2 b,
    simp [Hb'],
  have Hb : bc b = 0,
    have H4 : fc.symm (fc (bc b)) = 0,
      rw H3,
      have H5 : fc (0 : C) = 0 := is_add_group_hom.zero fc,
      rw ←H5,
      simp,
    simp only [equiv.inverse_apply_apply fc] at H4,
    exact H4,
  cases H4exact b Hb with a Ha,
  existsi (fa a),
  split,
  { show ab' (fa a) = b',
    rw ←H1,
    rw Ha.1,
    exact equiv.apply_inverse_apply fb b'
  },
  intros a₁' Ha₁',
  have H4 := Ha.2 (fa.symm a₁'),
  suffices H5 : ab (fa.symm a₁') = b,
    rw ←(H4 H5),simp,
  apply equiv.to_fun.injective fb,
  rw H1,
  simp [Ha₁'],
end 

