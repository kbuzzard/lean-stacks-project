import tag009H -- to get definition of stalk, which is the only filtered colimit I care about right now
import tag009P -- presheaf of (commutative) rings on basis 
universe u 
--#print presheaf_on_basis_stalk 
--#print presheaf_on_basis_stalk.aux 
namespace presheaf_of_rings_on_basis_stalk

variables {X : Type u} [topological_space X] {B : set (set X)}
{HB : topological_space.is_topological_basis B}
-- goal : comm_ring (presheaf_on_basis_stalk (FPRB.to_presheaf_of_types_on_basis) x) 

def stalk (FPRB : presheaf_of_rings_on_basis HB)
(x : X)
(Hstandard : ∀ U V ∈ B, U ∩ V ∈ B)
:= presheaf_on_basis_stalk (FPRB.to_presheaf_of_types_on_basis) x
def stalk.aux (FPRB : presheaf_of_rings_on_basis HB)
(x : X)
(Hstandard : ∀ U V ∈ B, U ∩ V ∈ B)
:= presheaf_on_basis_stalk.aux (FPRB.to_presheaf_of_types_on_basis) x

-- need this instance because a stalk.aux of a presheaf of types is a setoid
-- but I have a presheaf of rings
-- I guess I could have had presheaf of rings coe to presheaf of types?
variables (FPRB : presheaf_of_rings_on_basis HB) (x : X) (Hstandard : ∀ U V ∈ B, U ∩ V ∈ B)
include FPRB x Hstandard 

instance stalk_is_setoid
 : setoid (stalk.aux FPRB x Hstandard) := presheaf_on_basis_stalk.setoid FPRB.to_presheaf_of_types_on_basis x

private def add_aux : stalk.aux FPRB x Hstandard → stalk.aux FPRB x Hstandard → stalk FPRB x Hstandard := 
λ s t,⟦⟨s.U ∩ t.U,Hstandard s.U t.U s.BU t.BU,⟨s.Hx,t.Hx⟩,
        FPRB.res s.BU _   (set.inter_subset_left _ _) s.s +
        FPRB.res t.BU _   (set.inter_subset_right _ _) t.s
      ⟩⟧ 

instance ring_stalk_has_add : has_add (stalk FPRB x Hstandard) :=
⟨quotient.lift₂ (add_aux FPRB x Hstandard) (λ a₁ a₂ b₁ b₂ H1 H2,
  let U1 := classical.some H1 in
  let U2 := classical.some H2 in
  quotient.sound ⟨U1 ∩ U2,begin
    have H1' := classical.some_spec H1,
    cases H1' with Hx1 H1',
    cases H1' with BU1 H1',
    cases H1' with HUa₁ H1',
    cases H1' with HUb₁ H1',
    have H2' := classical.some_spec H2,
    cases H2' with Hx2 H2',
    cases H2' with BU2 H2',
    cases H2' with HUa₂ H2',
    cases H2' with HUb₂ H2',
    existsi (⟨Hx1,Hx2⟩ : x ∈ U1 ∩ U2),
    existsi Hstandard _ _ BU1 BU2,
    existsi set.inter_subset_inter HUa₁ HUa₂,
    existsi set.inter_subset_inter HUb₁ HUb₂,
    rw (FPRB.res_is_ring_morphism _ _ _).map_add,
    rw (FPRB.res_is_ring_morphism _ _ _).map_add,
    show (FPRB.res _ _ _ ∘ FPRB.res _ _ _) (a₁.s) +
         (FPRB.res _ _ _ ∘ FPRB.res _ _ _) (a₂.s) =
         (FPRB.res _ _ _ ∘ FPRB.res _ _ _) (b₁.s) +
         (FPRB.res _ _ _ ∘ FPRB.res _ _ _) (b₂.s),
    rw ←FPRB.Hcomp,
    rw ←FPRB.Hcomp,
    rw ←FPRB.Hcomp,
    rw ←FPRB.Hcomp,
    suffices : (FPRB.res BU1 (Hstandard U1 U2 BU1 BU2) (set.inter_subset_left _ _) ∘ FPRB.res a₁.BU BU1 HUa₁) (a₁.s) +
      (FPRB.res BU2 (Hstandard U1 U2 BU1 BU2) (set.inter_subset_right _ _) ∘ FPRB.res a₂.BU BU2 HUa₂) (a₂.s) =
      (FPRB.res BU1 (Hstandard U1 U2 BU1 BU2) (set.inter_subset_left _ _) ∘ FPRB.res b₁.BU BU1 HUb₁) (b₁.s) +
      (FPRB.res BU2 (Hstandard U1 U2 BU1 BU2) (set.inter_subset_right _ _) ∘ FPRB.res b₂.BU BU2 HUb₂) (b₂.s),
    rwa [←FPRB.Hcomp,←FPRB.Hcomp,←FPRB.Hcomp,←FPRB.Hcomp] at this,
    simp [H1',H2']
  end⟩)⟩

  --#check is_ring_hom

private def neg_aux : stalk.aux FPRB x Hstandard → stalk FPRB x Hstandard := 
λ s,⟦⟨s.U,s.BU,s.Hx,-s.s⟩⟧

instance : has_neg (stalk FPRB x Hstandard) :=
⟨quotient.lift (neg_aux FPRB x Hstandard) $ begin
  intros a b H,
  apply quotient.sound,
  cases H with U H,
  existsi U,
  cases H with Hx H,
  existsi Hx,
  cases H with BW H,
  existsi BW,
  cases H with HWU H,
  existsi HWU,
  cases H with HWV H,
  existsi HWV,
  show FPRB.res _ _ _ (-a.s) = FPRB.res _ _ _ (-b.s),
  have Ha : FPRB.res _ BW HWU (-a.s) = -(FPRB.res _ BW HWU a.s),
    rw @is_ring_hom.map_neg _ _ _ _ _ (FPRB.res_is_ring_morphism _ _ _),
  rw [Ha,H],
  rw @is_ring_hom.map_neg _ _ _ _ _ (FPRB.res_is_ring_morphism _ _ _),
end⟩

--#check @is_ring_hom.map_neg 

private def mul_aux : stalk.aux FPRB x Hstandard → stalk.aux FPRB x Hstandard → stalk FPRB x Hstandard := 
λ s t,⟦⟨s.U ∩ t.U,Hstandard s.U t.U s.BU t.BU,⟨s.Hx,t.Hx⟩,
        FPRB.res s.BU _   (set.inter_subset_left _ _) s.s *
        FPRB.res t.BU _   (set.inter_subset_right _ _) t.s
      ⟩⟧ 

instance ring_stalk_has_mul : has_mul (stalk FPRB x Hstandard) :=
⟨quotient.lift₂ (mul_aux FPRB x Hstandard) (λ a₁ a₂ b₁ b₂ H1 H2,
  let U1 := classical.some H1 in
  let U2 := classical.some H2 in
  quotient.sound ⟨U1 ∩ U2,begin
    have H1' := classical.some_spec H1,
    cases H1' with Hx1 H1',
    cases H1' with BU1 H1',
    cases H1' with HUa₁ H1',
    cases H1' with HUb₁ H1',
    have H2' := classical.some_spec H2,
    cases H2' with Hx2 H2',
    cases H2' with BU2 H2',
    cases H2' with HUa₂ H2',
    cases H2' with HUb₂ H2',
    existsi (⟨Hx1,Hx2⟩ : x ∈ U1 ∩ U2),
    existsi Hstandard _ _ BU1 BU2,
    existsi set.inter_subset_inter HUa₁ HUa₂,
    existsi set.inter_subset_inter HUb₁ HUb₂,
    rw (FPRB.res_is_ring_morphism _ _ _).map_mul,
    rw (FPRB.res_is_ring_morphism _ _ _).map_mul,
    show (FPRB.res _ _ _ ∘ FPRB.res _ _ _) (a₁.s) *
         (FPRB.res _ _ _ ∘ FPRB.res _ _ _) (a₂.s) =
         (FPRB.res _ _ _ ∘ FPRB.res _ _ _) (b₁.s) *
         (FPRB.res _ _ _ ∘ FPRB.res _ _ _) (b₂.s),
    rw ←FPRB.Hcomp,
    rw ←FPRB.Hcomp,
    rw ←FPRB.Hcomp,
    rw ←FPRB.Hcomp,
    suffices : (FPRB.res BU1 (Hstandard U1 U2 BU1 BU2) (set.inter_subset_left _ _) ∘ FPRB.res a₁.BU BU1 HUa₁) (a₁.s) *
      (FPRB.res BU2 (Hstandard U1 U2 BU1 BU2) (set.inter_subset_right _ _) ∘ FPRB.res a₂.BU BU2 HUa₂) (a₂.s) =
      (FPRB.res BU1 (Hstandard U1 U2 BU1 BU2) (set.inter_subset_left _ _) ∘ FPRB.res b₁.BU BU1 HUb₁) (b₁.s) *
      (FPRB.res BU2 (Hstandard U1 U2 BU1 BU2) (set.inter_subset_right _ _) ∘ FPRB.res b₂.BU BU2 HUb₂) (b₂.s),
    rwa [←FPRB.Hcomp,←FPRB.Hcomp,←FPRB.Hcomp,←FPRB.Hcomp] at this,
    simp [H1',H2']
  end⟩)⟩

lemma x_in_basis_elt : ∃ U ∈ B, x ∈ U :=
begin
have H1 := HB.2.1.symm,
have H2 : x ∈ @set.univ X := trivial,
rw H1 at H2,
cases H2 with U HU,
existsi U,
existsi HU.fst,
exact HU.snd
end 

private def zero : stalk FPRB x Hstandard := 
⟦⟨classical.some (x_in_basis_elt FPRB x Hstandard),
--  sorry,
   (classical.some_spec (x_in_basis_elt FPRB x Hstandard)).fst,
   (classical.some_spec (x_in_basis_elt FPRB x Hstandard)).snd,
   0
   ⟩⟧

private def one : stalk FPRB x Hstandard := 
⟦⟨classical.some (x_in_basis_elt FPRB x Hstandard),
--  sorry,
   (classical.some_spec (x_in_basis_elt FPRB x Hstandard)).fst,
   (classical.some_spec (x_in_basis_elt FPRB x Hstandard)).snd,
   1
   ⟩⟧

--set_option pp.notation false 
lemma r_of_eq : ∀ a b : (stalk.aux FPRB x Hstandard), a = b → a ≈ b := begin
intros a b Hab,
rw Hab,
end 

/-
lemma eq_eta : ∀ sU tU sBU tBU sHx tHx ss ts,ss = ts → 
  (⟨sU,sBU,sHx,ss⟩ : (stalk.aux FPRB x Hstandard)) = ⟨tU,tBU,tHx,ts⟩ :=
  begin
sorry 
  end
-/
--set_option pp.universes true
--set_option pp.proofs true
set_option trace.app_builder true
theorem stalks_of_presheaf_of_rings_on_basis_are_rings
-- {X : Type u} [topological_space X] {B : set (set X)}
--{HB : topological_space.is_topological_basis B} (FPRB : presheaf_of_rings_on_basis HB) (x : X) :
: comm_ring (stalk FPRB x Hstandard) := begin
refine {
  add := has_add.add,
--  add := (presheaf_of_rings_on_basis_stalk.ring_stalk_has_add FPRB x Hstandard).add,
  add_assoc := _,
  zero := (zero FPRB x Hstandard),
  zero_add := _,
  add_zero := _,
  neg := has_neg.neg,
  add_left_neg := _,
  add_comm := _,
  mul := has_mul.mul,
--  mul := (presheaf_of_rings_on_basis_stalk.ring_stalk_has_mul FPRB x Hstandard).mul,
  mul_assoc := _,
  mul_one := _,
  one := (one FPRB x Hstandard),
  one_mul := _,
  left_distrib := _,
  right_distrib := _,
  mul_comm := _,
},
show ∀ (a b c : stalk FPRB x Hstandard), a + b + c = a + (b + c),
{ intros a1 b1 c1,
  refine quotient.induction_on₃ a1 b1 c1 _,
  intros,
  cases a with Ua BUa Hxa sa,
  cases b with Ub BUb Hxb sb,
  cases c with Uc BUc Hxc sc,
  refine quotient.sound _,
  dsimp,refine r_of_eq FPRB x Hstandard _ _ _,
  rw presheaf_on_basis_stalk.aux.mk.inj_eq,
  split,
    cc,
  rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
  rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
  rw ←presheaf_of_types_on_basis.Hcomp',
  rw ←presheaf_of_types_on_basis.Hcomp',
  rw ←presheaf_of_types_on_basis.Hcomp',
  rw ←presheaf_of_types_on_basis.Hcomp',
  rw ←add_assoc,
    
  have Htemp1 : Ua ∩ Ub ∩ Uc ∈ B,
    apply Hstandard,
    apply Hstandard,
    exact BUa,
    exact BUb,
    exact BUc,
  have Htemp2 : Ua ∩ (Ub ∩ Uc) ∈ B,
    apply Hstandard,
    exact BUa,
    apply Hstandard,
    exact BUb,
    exact BUc,
  have Hinter : Ua ∩ Ub ∩ Uc = Ua ∩ (Ub ∩ Uc),
    cc,
  show (FPRB.to_presheaf_of_types_on_basis).res BUa Htemp1 _ sa + (FPRB.to_presheaf_of_types_on_basis).res BUb Htemp1 _ sb +
      (FPRB.to_presheaf_of_types_on_basis).res BUc Htemp1 _ sc ==
    (FPRB.to_presheaf_of_types_on_basis).res BUa Htemp2 _ sa + (FPRB.to_presheaf_of_types_on_basis).res BUb Htemp2 _ sb +
      (FPRB.to_presheaf_of_types_on_basis).res BUc Htemp2 _ sc,
  refine eq.drec_on Hinter _,
  let UU := Ua ∩ Ub ∩ Uc,
  have HI2 : UU = Ua ∩ (Ub ∩ Uc) := Hinter,
  congr,
  subst HI2,

  /-
  exact @eq.drec_on _ (Ua ∩ Ub ∩ Uc) (λ s h,
    (FPRB.to_presheaf_of_types_on_basis).res BUa Htemp1 _ sa +
        (FPRB.to_presheaf_of_types_on_basis).res BUb Htemp1 _ sb +
      (FPRB.to_presheaf_of_types_on_basis).res BUc Htemp1 _ sc ==
    (FPRB.to_presheaf_of_types_on_basis).res BUa (h ▸ Htemp1) _ sa +
        (FPRB.to_presheaf_of_types_on_basis).res BUb (h ▸ Htemp1) _ sb +
      (FPRB.to_presheaf_of_types_on_basis).res BUc (h ▸ Htemp1) _ sc
  ) _ Hinter (heq.refl _),
  -/
  --congr,
  --subst Hinter,
  --rw Hinter at Htemp1,
 
  --congr,
  
--  apply eq.mpr presheaf_on_basis_stalk.aux.mk.inj_eq,
--  generalize : 
--    (FPRB.to_presheaf_of_types_on_basis).res _ _ _ sa +
--    ((FPRB.to_presheaf_of_types_on_basis).res _ _ _ sb + (FPRB.to_presheaf_of_types_on_basis).res _ _ _ sc)
--    = ss,
--  generalize : 
--    (FPRB.to_presheaf_of_types_on_basis).res _ _ _ sa +
--    ((FPRB.to_presheaf_of_types_on_basis).res _ _ _ sb + (FPRB.to_presheaf_of_types_on_basis).res _ _ _ sc)
--    = ss,
     
--  subst H.symm,
--  refine eq.drec_on,
--  simp [H],

--  refine eq.drec_on H _,
  --congr,
},
repeat {sorry}, 
end

#print notation ==
#print heq_iff_eq
#check @presheaf_on_basis_stalk.aux.mk.inj_eq X
--{repeat {sorry}}

#exit 

--;{repeat {sorry}}


/-
import Kenny_comm_alg.direct_limit
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
