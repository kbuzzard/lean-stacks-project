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
(Hstandard : ∀ {{U V : set X}}, U ∈ B → V ∈ B → U ∩ V ∈ B)
(Hall : set.univ ∈ B)
:= presheaf_on_basis_stalk (FPRB.to_presheaf_of_types_on_basis) x

def stalk.aux (FPRB : presheaf_of_rings_on_basis HB)
(x : X)
(Hstandard : ∀ {{U V : set X}}, U ∈ B → V ∈ B → U ∩ V ∈ B)
(Hall : set.univ ∈ B)
:= presheaf_on_basis_stalk.aux (FPRB.to_presheaf_of_types_on_basis) x

-- need this instance because a stalk.aux of a presheaf of types is a setoid
-- but I have a presheaf of rings
-- I guess I could have had presheaf of rings coe to presheaf of types?
variables (FPRB : presheaf_of_rings_on_basis HB) (x : X)
(Hstandard : ∀ {{U V : set X}}, U ∈ B → V ∈ B → U ∩ V ∈ B)
(Hall : set.univ ∈ B)
include FPRB x Hstandard Hall

instance stalk_is_setoid
 : setoid (stalk.aux FPRB x Hstandard Hall) := presheaf_on_basis_stalk.setoid FPRB.to_presheaf_of_types_on_basis x

private def add_aux : stalk.aux FPRB x Hstandard Hall → stalk.aux FPRB x Hstandard Hall → stalk FPRB x Hstandard Hall := 
λ s t,⟦⟨s.U ∩ t.U,Hstandard s.BU t.BU,⟨s.Hx,t.Hx⟩,
        FPRB.res s.BU _   (set.inter_subset_left _ _) s.s +
        FPRB.res t.BU _   (set.inter_subset_right _ _) t.s
      ⟩⟧ 

instance ring_stalk_has_add : has_add (stalk FPRB x Hstandard Hall) :=
⟨quotient.lift₂ (add_aux FPRB x Hstandard Hall) (λ a₁ a₂ b₁ b₂ H1 H2,
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
    existsi Hstandard BU1 BU2,
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
    suffices : (FPRB.res BU1 (Hstandard BU1 BU2) (set.inter_subset_left _ _) ∘ FPRB.res a₁.BU BU1 HUa₁) (a₁.s) +
      (FPRB.res BU2 (Hstandard BU1 BU2) (set.inter_subset_right _ _) ∘ FPRB.res a₂.BU BU2 HUa₂) (a₂.s) =
      (FPRB.res BU1 (Hstandard BU1 BU2) (set.inter_subset_left _ _) ∘ FPRB.res b₁.BU BU1 HUb₁) (b₁.s) +
      (FPRB.res BU2 (Hstandard BU1 BU2) (set.inter_subset_right _ _) ∘ FPRB.res b₂.BU BU2 HUb₂) (b₂.s),
    rwa [←FPRB.Hcomp,←FPRB.Hcomp,←FPRB.Hcomp,←FPRB.Hcomp] at this,
    simp [H1',H2']
  end⟩)⟩

  --#check is_ring_hom

private def neg_aux : stalk.aux FPRB x Hstandard Hall → stalk FPRB x Hstandard Hall := 
λ s,⟦⟨s.U,s.BU,s.Hx,-s.s⟩⟧

instance : has_neg (stalk FPRB x Hstandard Hall) :=
⟨quotient.lift (neg_aux FPRB x Hstandard Hall) $ begin
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

private def mul_aux : stalk.aux FPRB x Hstandard Hall → stalk.aux FPRB x Hstandard Hall → stalk FPRB x Hstandard Hall:= 
λ s t,⟦⟨s.U ∩ t.U,Hstandard s.BU t.BU,⟨s.Hx,t.Hx⟩,
        FPRB.res s.BU _   (set.inter_subset_left _ _) s.s *
        FPRB.res t.BU _   (set.inter_subset_right _ _) t.s
      ⟩⟧ 

instance ring_stalk_has_mul : has_mul (stalk FPRB x Hstandard Hall) :=
⟨quotient.lift₂ (mul_aux FPRB x Hstandard Hall) (λ a₁ a₂ b₁ b₂ H1 H2,
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
    existsi Hstandard BU1 BU2,
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
    suffices : (FPRB.res BU1 (Hstandard BU1 BU2) (set.inter_subset_left _ _) ∘ FPRB.res a₁.BU BU1 HUa₁) (a₁.s) *
      (FPRB.res BU2 (Hstandard BU1 BU2) (set.inter_subset_right _ _) ∘ FPRB.res a₂.BU BU2 HUa₂) (a₂.s) =
      (FPRB.res BU1 (Hstandard BU1 BU2) (set.inter_subset_left _ _) ∘ FPRB.res b₁.BU BU1 HUb₁) (b₁.s) *
      (FPRB.res BU2 (Hstandard BU1 BU2) (set.inter_subset_right _ _) ∘ FPRB.res b₂.BU BU2 HUb₂) (b₂.s),
    rwa [←FPRB.Hcomp,←FPRB.Hcomp,←FPRB.Hcomp,←FPRB.Hcomp] at this,
    simp [H1',H2']
  end⟩)⟩

/-
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
-/

private def zero : stalk FPRB x Hstandard Hall := 
⟦⟨set.univ,Hall,trivial,0⟩⟧

instance ring_stalk_has_zero : has_zero (stalk FPRB x Hstandard Hall) := ⟨zero FPRB x Hstandard Hall⟩

private def one : stalk FPRB x Hstandard Hall := 
⟦⟨set.univ,Hall,trivial,1⟩⟧

instance ring_stalk_has_one : has_one (stalk FPRB x Hstandard Hall) := ⟨one FPRB x Hstandard Hall⟩

/-
lemma r_of_eq : ∀ a b : (stalk.aux FPRB x Hstandard Hall), a = b → a ≈ b := begin
intros a b Hab,
rw Hab,
end 
-/

/-
lemma eq_eta : ∀ sU tU sBU tBU sHx tHx ss ts,ss = ts → 
  (⟨sU,sBU,sHx,ss⟩ : (stalk.aux FPRB x Hstandard)) = ⟨tU,tBU,tHx,ts⟩ :=
  begin
sorry 
  end
-/

instance stalks_of_presheaf_of_rings_on_basis_are_rings
-- {X : Type u} [topological_space X] {B : set (set X)}
--{HB : topological_space.is_topological_basis B} (FPRB : presheaf_of_rings_on_basis HB) (x : X) :
: comm_ring (stalk FPRB x Hstandard Hall) := begin
  refine {
    add := has_add.add,
    add_assoc := _,
    zero := (zero FPRB x Hstandard Hall),
    zero_add := _,
    add_zero := _,
    neg := has_neg.neg,
    add_left_neg := _,
    add_comm := _,
    mul := has_mul.mul,
    mul_assoc := _,
    mul_one := _,
    one := (one FPRB x Hstandard Hall),
    one_mul := _,
    left_distrib := _,
    right_distrib := _,
    mul_comm := _,
  },
  show ∀ (a b c : stalk FPRB x Hstandard Hall), a + b + c = a + (b + c),
  { intros a1 b1 c1,
    refine quotient.induction_on₃ a1 b1 c1 _,
    intros,
    cases a with Ua BUa Hxa sa,
    cases b with Ub BUb Hxb sb,
    cases c with Uc BUc Hxc sc,
    refine quotient.sound _,
    dsimp,
    existsi (Ua ∩ Ub ∩ Uc), -- brainwave
    existsi (⟨⟨Hxa,Hxb⟩,Hxc⟩ : x ∈ Ua ∩ Ub ∩ Uc),
    existsi (Hstandard (Hstandard BUa BUb) BUc),
    existsi (set.subset.refl (Ua ∩ Ub ∩ Uc)),
    existsi ((set.inter_assoc Ua Ub Uc ▸ set.subset.refl _) : Ua ∩ Ub ∩ Uc ⊆ Ua ∩ (Ub ∩ Uc)),
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←(presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw add_assoc,
  --    simp [add_assoc,add_comm],rw add_comm, -- also works!
  },
  show ∀ (a : stalk FPRB x Hstandard Hall), 0 + a = a,
  { intro a1,
    refine quotient.induction_on a1 _,
    intro a,
    cases a with Ua BUa Hxa sa,
    refine quotient.sound _,
    dsimp,
    existsi (set.univ ∩ Ua), 
    existsi ( ⟨trivial,Hxa⟩ : x ∈ set.univ ∩ Ua),
    existsi (Hstandard Hall BUa : set.univ ∩ Ua ∈ B),
    existsi (_ : set.univ ∩ Ua ⊆ set.univ ∩ Ua),tactic.swap,rw set.inter_comm,
    existsi _,tactic.swap, rw set.univ_inter Ua,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw is_ring_hom.map_zero (FPRB.res _ _ _);try {apply_instance},
    -- (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_zero,
    rw zero_add,
  },
  show ∀ (a : stalk FPRB x Hstandard Hall), a + 0 = a,
  { intro a1,
    refine quotient.induction_on a1 _,
    intro a,
    cases a with Ua BUa Hxa sa,
    refine quotient.sound _,
    dsimp,
    existsi (Ua ∩ set.univ), 
    existsi ( ⟨Hxa,trivial⟩ : x ∈ Ua ∩ set.univ),
    existsi (Hstandard BUa Hall : Ua ∩ set.univ ∈ B),
    existsi (_ : Ua ∩ set.univ ⊆ Ua ∩ set.univ),tactic.swap,rw set.inter_comm,
    existsi _,tactic.swap, rw set.inter_univ Ua,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw is_ring_hom.map_zero (FPRB.res _ _ _);try {apply_instance},
    -- (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_zero,
    rw add_zero
  },
  show ∀ (a : stalk FPRB x Hstandard Hall), -a + a = 0,
  { intro a1,
    refine quotient.induction_on a1 _,
    intro a,
    cases a with Ua BUa Hxa sa,
    refine quotient.sound _,
    dsimp,
    existsi (Ua ∩ Ua), 
    existsi _,tactic.swap, exact ⟨Hxa,Hxa⟩,
    existsi _,tactic.swap, exact Hstandard BUa BUa,
    existsi _,tactic.swap, exact set.subset.refl _,
    existsi _,tactic.swap, exact set.subset.trans (set.inter_subset_left _ _) (set.subset_univ _),
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw is_ring_hom.map_neg (FPRB.res _ _ _);try {apply_instance},
    rw add_left_neg,
    rw is_ring_hom.map_zero (FPRB.res _ _ _);try {apply_instance}
  },
  show ∀ (a b : stalk FPRB x Hstandard Hall), a + b = b + a,
  { intros a1 b1,
    refine quotient.induction_on₂ a1 b1 _,
    intros a b,
    cases a with Ua BUa Hxa sa,
    cases b with Ub BUb Hxb sb,
    refine quotient.sound _,
    dsimp,
    existsi (Ua ∩ Ub), -- brainwave
    existsi (⟨Hxa,Hxb⟩ : x ∈ Ua ∩ Ub),
    existsi (Hstandard BUa BUb),
    existsi (set.subset.refl (Ua ∩ Ub)),
    existsi ((set.inter_comm Ua Ub ▸ set.subset.refl _) : Ua ∩ Ub ⊆ Ub ∩ Ua),
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add,
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw add_comm
  },
  show ∀ (a b c : stalk FPRB x Hstandard Hall), a * b * c = a * (b * c),
  { intros a1 b1 c1,
    refine quotient.induction_on₃ a1 b1 c1 _,
    intros,
    cases a with Ua BUa Hxa sa,
    cases b with Ub BUb Hxb sb,
    cases c with Uc BUc Hxc sc,
    refine quotient.sound _,
    dsimp,
    existsi (Ua ∩ Ub ∩ Uc),
    existsi (⟨⟨Hxa,Hxb⟩,Hxc⟩ : x ∈ Ua ∩ Ub ∩ Uc),
    existsi (Hstandard (Hstandard BUa BUb) BUc),
    existsi (set.subset.refl (Ua ∩ Ub ∩ Uc)),
    existsi ((set.inter_assoc Ua Ub Uc ▸ set.subset.refl _) : Ua ∩ Ub ∩ Uc ⊆ Ua ∩ (Ub ∩ Uc)),
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul,
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw mul_assoc
  },
  show ∀ (a : stalk FPRB x Hstandard Hall), _ * a = a, -- 1
  { intro a1,
    refine quotient.induction_on a1 _,
    intro a,
    cases a with Ua BUa Hxa sa,
    refine quotient.sound _,
    dsimp,
    existsi (set.univ ∩ Ua), 
    existsi ( ⟨trivial,Hxa⟩ : x ∈ set.univ ∩ Ua),
    existsi (Hstandard Hall BUa : set.univ ∩ Ua ∈ B),
    existsi (_ : set.univ ∩ Ua ⊆ set.univ ∩ Ua),tactic.swap,rw set.inter_comm,
    existsi _,tactic.swap, rw set.univ_inter Ua,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul,
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw is_ring_hom.map_one (FPRB.res _ _ _);try {apply_instance},
    rw one_mul,
  },
  show ∀ (a : stalk FPRB x Hstandard Hall), a * 1 = a,
  { intro a1,
    refine quotient.induction_on a1 _,
    intro a,
    cases a with Ua BUa Hxa sa,
    refine quotient.sound _,
    dsimp,
    existsi (Ua ∩ set.univ), 
    existsi ( ⟨Hxa,trivial⟩ : x ∈ Ua ∩ set.univ),
    existsi (Hstandard BUa Hall : Ua ∩ set.univ ∈ B),
    existsi (_ : Ua ∩ set.univ ⊆ Ua ∩ set.univ),tactic.swap,rw set.inter_comm,
    existsi _,tactic.swap, rw set.inter_univ Ua,
    rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul,
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw ←presheaf_of_types_on_basis.Hcomp',
    rw is_ring_hom.map_one (FPRB.res _ _ _);try {apply_instance},
    -- (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_zero,
    rw mul_one
  },
  show ∀ (a b c : stalk FPRB x Hstandard Hall), a * (b + c) = a * b + a * c,
  { intros a1 b1 c1,
    refine quotient.induction_on₃ a1 b1 c1 _,
    intros,
    cases a with Ua BUa Hxa sa,
    cases b with Ub BUb Hxb sb,
    cases c with Uc BUc Hxc sc,
    refine quotient.sound _,
    dsimp,
    existsi (Ua ∩ Ub ∩ Uc), -- brainwave
    existsi (⟨⟨Hxa,Hxb⟩,Hxc⟩ : x ∈ Ua ∩ Ub ∩ Uc),
    existsi (Hstandard (Hstandard BUa BUb) BUc),
    existsi ((set.inter_assoc Ua Ub Uc ▸ set.subset.refl _) : Ua ∩ Ub ∩ Uc ⊆ Ua ∩ (Ub ∩ Uc)),
    existsi _,tactic.swap, show (Ua ∩ Ub ∩ Uc ⊆ Ua ∩ Ub ∩ (Ua ∩ Uc)),
      intros y Hy,cases Hy with Hab Hc, cases Hab with Ha Hb,
      exact ⟨⟨Ha,Hb⟩,⟨Ha,Hc⟩⟩,
    repeat {rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul},
    repeat {rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add},
    repeat {rw ←presheaf_of_types_on_basis.Hcomp'},
    repeat {rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul},
    repeat {rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add},
    repeat {rw ←presheaf_of_types_on_basis.Hcomp'},
    rw mul_add,
  },
  show ∀ (a b c : stalk FPRB x Hstandard Hall), (a + b) * c = a * c + b * c,
  { intros a1 b1 c1,
    refine quotient.induction_on₃ a1 b1 c1 _,
    intros,
    cases a with Ua BUa Hxa sa,
    cases b with Ub BUb Hxb sb,
    cases c with Uc BUc Hxc sc,
    refine quotient.sound _,
    dsimp,
    existsi (Ua ∩ Ub ∩ Uc), -- brainwave
    existsi (⟨⟨Hxa,Hxb⟩,Hxc⟩ : x ∈ Ua ∩ Ub ∩ Uc),
    existsi (Hstandard (Hstandard BUa BUb) BUc),
    existsi (set.subset.refl _),
    existsi _,tactic.swap, show (Ua ∩ Ub ∩ Uc ⊆ Ua ∩ Uc ∩ (Ub ∩ Uc)),
      intros y Hy,cases Hy with Hab Hc, cases Hab with Ha Hb,
      exact ⟨⟨Ha,Hc⟩,⟨Hb,Hc⟩⟩,
    repeat {rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul},
    repeat {rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add},
    repeat {rw ←presheaf_of_types_on_basis.Hcomp'},
    repeat {rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul},
    repeat {rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_add},
    repeat {rw ←presheaf_of_types_on_basis.Hcomp'},
    rw add_mul,
  },  
  -- last one!
  show ∀ (a b : stalk FPRB x Hstandard Hall), a * b = b * a,
  { intros a1 b1,
    refine quotient.induction_on₂ a1 b1 _,
    intros,
    cases a with Ua BUa Hxa sa,
    cases b with Ub BUb Hxb sb,
    refine quotient.sound _,
    dsimp,
    existsi (Ua ∩ Ub),
    existsi (⟨Hxa,Hxb⟩ : x ∈ Ua ∩ Ub),
    existsi (Hstandard BUa BUb),
    existsi (set.subset.refl _),
    existsi _,tactic.swap, rw set.inter_comm,
    repeat {rw (presheaf_of_rings_on_basis.res_is_ring_morphism FPRB _ _ _).map_mul},
    repeat {rw ←presheaf_of_types_on_basis.Hcomp'},
    rw mul_comm,
  },  
end
end presheaf_of_rings_on_basis_stalk