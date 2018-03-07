import analysis.topology.topological_space data.set
import analysis.topology.continuity 
import Kenny_comm_alg.Zariski
import Kenny_comm_alg.temp
import tag00EJ_statement
import localization
import localization_UMP
import tag00E0
import Kenny_comm_alg.temp

universes u v 
/-
structure ring_morphism {α : Type*} {β : Type*} (Ra : comm_ring α) (Rb : comm_ring β) (f : α → β) :=
(f_zero : f 0 = 0)
(f_one : f 1 = 1)
(f_add : ∀ {a₁ a₂ : α}, f (a₁ + a₂) = f a₁ + f a₂)
(f_mul : ∀ {a₁ a₂ : α}, f (a₁ * a₂) = f a₁ * f a₂) 
-/
local attribute [class] topological_space.is_open 

structure presheaf_of_types (α : Type*) [T : topological_space α] := 
(F : Π U : set α, T.is_open U → Type*)
(res : ∀ (U V : set α) (OU : T.is_open U) (OV : T.is_open V) (H : V ⊆ U), 
  (F U OU) → (F V OV))
(Hid : ∀ (U : set α) (OU : T.is_open U), (res U U OU _ (set.subset.refl U)) = id)  
(Hcomp : ∀ (U V W : set α) (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W)
  (HUV : V ⊆ U) (HVW : W ⊆ V),
  (res U W OU OW (set.subset.trans HVW HUV)) = (res V W OV _ HVW) ∘ (res U V _ _ HUV) )

structure presheaf_of_rings (α : Type*) [T : topological_space α] :=
(PT : presheaf_of_types α)
(Fring : ∀ U OU, comm_ring (PT.F U OU))
(res_is_ring_morphism : ∀ (U V : set α) (OU : T.is_open U) (OV : T.is_open V) (H : V ⊆ U),
  is_ring_hom (PT.res U V OU OV H)) 
--attribute [class] presheaf_of_rings
--attribute [instance] presheaf_of_rings.Fring
--local attribute [instance] topological_space.is_open_inter

definition presheaf_of_types_pushforward
  {α : Type*} [Tα : topological_space α]
  {β : Type*} [Tβ : topological_space β]
  (f : α → β)
  (fcont: continuous f)
  (FPT : presheaf_of_types α)
: presheaf_of_types β :=
  { F := λ V OV, FPT.F (f ⁻¹' V) (fcont V OV),
    res := λ V₁ V₂ OV₁ OV₂ H, 
      FPT.res (f ⁻¹' V₁) (f⁻¹' V₂) (fcont V₁ OV₁) (fcont V₂ OV₂) (λ x Hx,H Hx),
    Hid := λ V OV, FPT.Hid (f ⁻¹' V) (fcont V OV),
    Hcomp := λ Uβ Vβ Wβ OUβ OVβ OWβ HUV HVW,
      FPT.Hcomp (f ⁻¹' Uβ)(f ⁻¹' Vβ)(f ⁻¹' Wβ) (fcont Uβ OUβ) (fcont Vβ OVβ) (fcont Wβ OWβ)
      (λ x Hx, HUV Hx) (λ x Hx, HVW Hx)
  }

definition presheaf_of_rings_pushforward
  {α : Type*} [Tα : topological_space α]
  {β : Type*} [Tβ : topological_space β]
  (f : α → β)
  (fcont: continuous f)
  (FPR : presheaf_of_rings α)
  : presheaf_of_rings β :=
  { PT := presheaf_of_types_pushforward f fcont FPR.PT,
    Fring := λ U OU,FPR.Fring (f ⁻¹' U) (fcont U OU),
    res_is_ring_morphism := λ U V OU OV H,
      FPR.res_is_ring_morphism (f ⁻¹' U) (f ⁻¹' V) (fcont U OU) (fcont V OV) (λ x Hx, H Hx)
  }

structure open_immersion
  {α : Type*} [Tα : topological_space α]
  {β : Type*} [Tβ : topological_space β]
  (f : α → β) : Prop :=
(fcont : continuous f)
(finj : function.injective f)
(fopens : ∀ U : set α, is_open U ↔ is_open (f '' U))

--set_option pp.notation false 

lemma inclusion_of_inclusion
  {α : Type*} [Tα : topological_space α]
  {β : Type*} [Tβ : topological_space β]
  (f : α → β)
  (U V : set α)
  : (V ⊆ U) → (f '' V) ⊆ (f '' U) := λ H2 a ⟨x,Hx⟩,⟨x,H2 Hx.1,Hx.2⟩

lemma immersion_sends_opens_to_opens 
  {α : Type*} [Tα : topological_space α]
  {β : Type*} [Tβ : topological_space β]
  (f : α → β) (H : open_immersion f) : 
∀ U : set α, is_open U → is_open (f '' U) := λ U OU, (H.fopens U).1 OU

definition presheaf_of_types_pullback_under_open_immersion
  {α : Type*} [Tα : topological_space α]
  {β : Type*} [Tβ : topological_space β]
  (PT : presheaf_of_types β)
  (f : α → β)
  (H : open_immersion f)
: presheaf_of_types α := {
F := λ U HU,PT.F (f '' U) ((H.fopens U).1 HU),
res := λ U V OU OV H2,PT.res (f '' U) (f '' V) ((H.fopens U).1 OU) ((H.fopens V).1 OV)
  (inclusion_of_inclusion f U V H2),
Hid := λ _ _,PT.Hid _ _,
Hcomp := λ U V W _ _ _ HUV HVW, 
  PT.Hcomp _ _ _ _ _ _ (inclusion_of_inclusion f U V HUV) (inclusion_of_inclusion f V W HVW)
} 

definition presheaf_of_rings_pullback_under_open_immersion
  {α : Type*} [Tα : topological_space α]
  {β : Type*} [Tβ : topological_space β]
  (PR : presheaf_of_rings β)
  (f : α → β)
  (H : open_immersion f)
: presheaf_of_rings α := 
{ PT := presheaf_of_types_pullback_under_open_immersion PR.PT f H,
  Fring := λ U OU,PR.Fring (f '' U) (immersion_sends_opens_to_opens f H U OU),
  res_is_ring_morphism := λ U V OU OV H2,PR.res_is_ring_morphism (f '' U) (f '' V)
    (immersion_sends_opens_to_opens f H U OU)
    (immersion_sends_opens_to_opens f H V OV) 
    (inclusion_of_inclusion f U V H2),
} 

structure morphism_of_presheaves_of_types {α : Type*} [Tα : topological_space α] 
(FPT : presheaf_of_types α) (GPT : presheaf_of_types α)
:= 
(morphism : ∀ U : set α, ∀ HU : Tα.is_open U, (FPT.F U HU) → GPT.F U HU)
(commutes : ∀ U V : set α, ∀ HU : Tα.is_open U, ∀ HV : Tα.is_open V, ∀ Hsub : V ⊆ U,
  (GPT.res U V HU HV Hsub) ∘ (morphism U HU) = (morphism V HV) ∘ (FPT.res U V HU HV Hsub))

structure morphism_of_presheaves_of_rings {α : Type*} [Tα : topological_space α]
(FPR : presheaf_of_rings α) (GPR : presheaf_of_rings α)
:=
(morphism : morphism_of_presheaves_of_types FPR.PT GPR.PT)
(ring_homs : ∀ U : set α, ∀ HU : is_open U, 
  @is_ring_hom _ _ (FPR.Fring U HU) (GPR.Fring U HU) (morphism.morphism U HU))

def composition_of_morphisms_of_presheaves_of_types {α : Type*} [Tα : topological_space α]
  {FPT GPT HPT : presheaf_of_types α} (fg : morphism_of_presheaves_of_types FPT GPT)
  (gh : morphism_of_presheaves_of_types GPT HPT)
: morphism_of_presheaves_of_types FPT HPT :=
  { morphism := λ U HU, gh.morphism U HU ∘ fg.morphism U HU,
    commutes := λ U V HU HV Hsub, begin
    show (HPT.res U V HU HV Hsub ∘ gh.morphism U HU) ∘ fg.morphism U HU =
    gh.morphism V HV ∘ (fg.morphism V HV ∘ FPT.res U V HU HV Hsub),
    rw gh.commutes U V HU HV Hsub,
    rw ←fg.commutes U V HU HV Hsub,
    end
  }

def identity_morphism_of_presheaves_of_types {α : Type*} [Tα : topological_space α]
  (FPT : presheaf_of_types α) : morphism_of_presheaves_of_types FPT FPT :=
  { morphism := λ _ _,id,
    commutes := λ _ _ _ _ _,rfl
  }

def are_isomorphic_presheaves_of_types {α : Type} [Tα : topological_space α]
(FPT : presheaf_of_types α) (GPT : presheaf_of_types α)
: Prop 
:= 
∃ fg : morphism_of_presheaves_of_types FPT GPT,
∃ gf : morphism_of_presheaves_of_types GPT FPT, 
  composition_of_morphisms_of_presheaves_of_types fg gf = identity_morphism_of_presheaves_of_types FPT
  ∧ composition_of_morphisms_of_presheaves_of_types gf fg = identity_morphism_of_presheaves_of_types GPT

def are_isomorphic_presheaves_of_rings {α : Type} [Tα : topological_space α]
(FPR : presheaf_of_rings α) (GPR : presheaf_of_rings α)
: Prop
:= 
∃ fg : morphism_of_presheaves_of_rings FPR GPR,
∃ gf : morphism_of_presheaves_of_rings GPR FPR, 
  composition_of_morphisms_of_presheaves_of_types fg.morphism gf.morphism = identity_morphism_of_presheaves_of_types FPR.PT
  ∧ composition_of_morphisms_of_presheaves_of_types gf.morphism fg.morphism = identity_morphism_of_presheaves_of_types GPR.PT


def res_to_inter_left {α : Type*} [T : topological_space α] 
  (FT : presheaf_of_types α)
  (U V : set α) [OU : T.is_open U] [OV : T.is_open V] 
  : (FT.F U OU) → (FT.F (U ∩ V) (T.is_open_inter U V OU OV)) 
  := FT.res U (U ∩ V) OU (T.is_open_inter U V OU OV) (set.inter_subset_left U V)

def res_to_inter_right {α : Type*} [T : topological_space α]
  (FT : presheaf_of_types α)
  (U V : set α) [OU : T.is_open U] [OV : T.is_open V]
  : (FT.F V OV) → (FT.F (U ∩ V) (T.is_open_inter U V OU OV)) 
  := FT.res V (U ∩ V) OV (T.is_open_inter U V OU OV) (set.inter_subset_right U V)

def gluing {α : Type*} [T : topological_space α] (FP : presheaf_of_types α) 
  (U :  set α)
  [UO : T.is_open U]
  {γ : Type*} (Ui : γ → set α)
  [UiO : ∀ i : γ, T.is_open (Ui i)]
  (Hcov : (⋃ (x : γ), (Ui x)) = U) 
  : (FP.F U UO) → 
    {a : (Π (x : γ), (FP.F (Ui x) (UiO x))) | ∀ (x y : γ), 
      (res_to_inter_left FP (Ui x) (Ui y)) (a x) = 
      (res_to_inter_right FP (Ui x) (Ui y)) (a y)} :=
λ r,⟨λ x,(FP.res U (Ui x) UO (UiO x) (Hcov ▸ set.subset_Union Ui x) r),
  λ x₁ y₁,
  have Hopen : T.is_open ((Ui x₁) ∩ (Ui y₁)) := (T.is_open_inter _ _ (UiO x₁) (UiO y₁)),
show ((FP.res (Ui x₁) ((Ui x₁) ∩ (Ui y₁)) _ Hopen _) ∘ 
      (FP.res U (Ui x₁) _ _ _)) r =
    ((FP.res (Ui y₁) ((Ui x₁) ∩ (Ui y₁)) _ Hopen _) ∘ 
      (FP.res U (Ui y₁) _ _ _)) r,by rw [←presheaf_of_types.Hcomp,←presheaf_of_types.Hcomp]⟩

structure is_sheaf_of_types {α : Type*} [T : topological_space α]
  (PT : presheaf_of_types α) : Prop :=
(Fsheaf : ∀ (U : set α) [OU : T.is_open U] 
          {γ : Type*} (Ui : γ → set α)
          [UiO : ∀ x : γ, T.is_open (Ui x)] 
          (Hcov : (⋃ (x : γ), (Ui x)) = U),
        function.bijective (gluing PT U Ui Hcov)
)
/-- This is OK because exactness is same for sheaves of rings and sets-/
structure is_sheaf_of_rings {α : Type*} [T : topological_space α] 
  (PR : presheaf_of_rings α)
: Prop :=
(Fsheaf : is_sheaf_of_types PR.PT)

--theorem D_f_are_a_basis {R : Type u} [comm_ring R] : ∀ U : set (X R), topological_space.is_open (Zariski R) U → ∃ α : Type v, ∃ f : α → R, U = set.Union (Spec.D' ∘ f) := sorry

--definition structure_sheaf_on_union {R : Type u} [comm_ring R] {α : Type} (f : α → R) := 
--  {x : (Π i : α, localization.loc R (powers $ f i)) // ∀ j k : α, localise_more_left (f j) (f k) (x j) = localise_more_right (f j) (f k) (x k) } 

--#check topological_space.is_open 
--#check @localization.at_prime
-- #check @sheaf_of_rings 

#print Spec.V'
#print is_ring_hom 
#check @localization.away.extend_map_of_im_unit
#check localization.of_comm_ring
#check @localization.prime.is_submonoid
#check @localization.unit_of_in_S
#check localization.away.extend_map_of_im_unit.is_ring_hom


noncomputable definition canonical_map {R : Type*} [comm_ring R] (g : R) (u : X R) (H : u ∈ Spec.D' g) 
: localization.away g → @localization.at_prime R _ u.val u.property 
:= @localization.away.extend_map_of_im_unit _ _ _ _
     (@localization.of_comm_ring R _ (set.compl u.val) (@localization.prime.is_submonoid _ _ u.val u.property))
     (_)
     g 
     (@localization.unit_of_in_S R _ (set.compl u.val) (@localization.prime.is_submonoid _ _ u.val u.property) ⟨g,H⟩)


  
  #check set.exists_mem_of_ne_empty

#check tag00E0.lemma14
/-
  ∀ (R : Type u_1) [_inst_1 : comm_ring R] (f : R) (I : set R) [_inst_2 : is_ideal I],
    f ∈ I → Spec.D' f ∩ Spec.V I = ∅
    -/
local attribute [instance] localization.away.extend_map_of_im_unit.is_ring_hom

--set_option pp.notation false 

definition structure_presheaf_of_types_on_affine_scheme (R : Type*) [comm_ring R] 
: presheaf_of_types (X R) :=
{ F := 

λ U HU, { f : Π P : X R, P ∈ U → @localization.at_prime R _ P.val P.property // 
  ∀ u : X R, U u → ∃ g : R, u ∈ Spec.D' g ∧ Spec.D' g ⊆ U ∧ ∃ r : localization.away g, ∀ Q : X R, 
  Π HQQ : Q ∈ U, Π H2 : Q ∈ Spec.D' g, f Q HQQ = canonical_map g Q H2 r }
  
--λ U HU, { f : Π P : {u : X ∈ Spec.D' g ∧ Spec.D' g ⊆ U ∧ ∃ r : localization.away g, ∀ v : {v : X R // U v},
--  Π H2 : v.val ∈ Spec.D' g, f ⟨v.val,v.property⟩ = canonical_map g v H2 r }
  
  ,
  res := λ U V OU OV H f,⟨λ P HP,f.val P (H HP),
  begin
    intros P HVP,
    -- P is in U, so existence of f says there exists g...
    cases f.property P (H HVP) with g Hg,
    -- P is in V, so there exists h such that P in D(h) in V by 00E0(14)
    cases OV with T HT,
    cases (tag00E0.cor_to_14 R T V HT P HVP) with h Hh,
      existsi (g*h),
      split,
      { -- proof that P is in D(gh)
        rw tag00E0.lemma15,
        exact ⟨Hg.1,Hh.1⟩
      },
      have H4 : set.subset (Spec.D' (g * h)) V,
      { -- proof that D(gh) is a sub of V
        rw tag00E0.lemma15,
        refine set.subset.trans _ Hh.2,
        exact set.inter_subset_right _ _,
      },      
      split, exact H4,
      cases Hg.2.2 with r Hr,
      -- r in R[1/g] but I need it in R[1/gh]
      existsi (localise_more_left g h r),
      intros Q HQ,
      -- Hr is the assertion that f is on both sides
      -- and this should boil down to f(Q) = f(Q)
      have H3 := Hr Q (H HQ),
      intro H2,
      have H5 := H2,rw tag00E0.lemma15 at H5,
      have H6 := H3 H5.1,
      rw H6,
      suffices : canonical_map g Q H5.left = (canonical_map (g * h) Q H2) ∘ (localise_more_left g h),
        exact congr_fun this r,
      apply eq.symm,
      unfold canonical_map,
      admit,
    end⟩,
  Hid := λ U OU,funext (λ f,subtype.eq (funext (λ P,rfl))),
  Hcomp := λ U V W OU OV OW HUV HVW,funext (λ f,subtype.eq (funext (λ P,rfl)))
}

definition structure_presheaf_value_is_comm_ring {R : Type*} [comm_ring R] (U : set (X R)) (HU : is_open U)
: comm_ring { f : Π P : X R, P ∈ U → @localization.at_prime R _ P.val P.property // 
  ∀ u : X R, U u → ∃ g : R, u ∈ Spec.D' g ∧ Spec.D' g ⊆ U ∧ ∃ r : localization.away g, ∀ Q : X R, 
  Π HQQ : Q ∈ U, Π H2 : Q ∈ Spec.D' g, f Q HQQ = canonical_map g Q H2 r }
:= {
  add := λ f₁ f₂, ⟨λ P HP, f₁.val P HP + f₂.val P HP,_⟩,
  mul := sorry,
  add_comm := sorry,
  zero := sorry,
  zero_add := sorry,
  add_zero := sorry,
  neg := sorry,
  add_left_neg := sorry,
  add_assoc := sorry,
  mul_assoc := sorry,
  one := sorry,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  mul_comm := sorry
}

definition structure_presheaf_of_rings_on_affine_scheme (R : Type*) [comm_ring R] 
: presheaf_of_rings (X R)
:= { PT := structure_presheaf_of_types_on_affine_scheme R,
    Fring := λ U OU,structure_presheaf_value_is_comm_ring U OU,
    res_is_ring_morphism := λ U V OU OV H, {
      map_add := sorry,
      map_mul := sorry,
      map_one := sorry
    }
}

definition structure_sheaf_of_rings_on_affine_scheme (R : Type*) [comm_ring R] 
: is_sheaf_of_rings (structure_presheaf_of_rings_on_affine_scheme R)
:= {
  Fsheaf := sorry, -- don't need this to define schemes.
}

structure scheme :=
(α : Type u)
(T : topological_space α)
(O_X : presheaf_of_rings α)
(O_X_sheaf : is_sheaf_of_rings O_X)
(locally_affine : ∃ β : Type v, ∃ cov : β → {U : set α // T.is_open U}, 
  set.Union (λ b, (cov b).val) = set.univ ∧
  ∀ b : β, ∃ R : Type*, ∃ RR : comm_ring R, ∃ fR : (X R) → α, 
    Π H : open_immersion fR, 
    are_isomorphic_presheaves_of_rings 
      (presheaf_of_rings_pullback_under_open_immersion O_X fR H)
      (structure_presheaf_of_rings_on_affine_scheme R)
)

#print axioms scheme 
/-
definition presheaf_of_rings_pullback_under_open_immersion
  {α : Type*} [Tα : topological_space α]
  (U : set α) (OU : is_open U)
  (FPT : presheaf_of_types α)
  (FPR : presheaf_of_rings (FPT))
  : presheaf_of_rings (presheaf_of_types_pullback_under_open_immersion U OU FPT) := sorry 
-/

-- now back to stuff not stolen from Patrick
/-
universes u v

theorem D_f_are_a_basis {R : Type u} [comm_ring R] : ∀ U : set (X R), topological_space.is_open (Zariski R) U → ∃ α : Type v, ∃ f : α → R, U = set.Union (Spec.D' ∘ f) := sorry

definition structure_sheaf_on_union {R : Type u} [comm_ring R] {α : Type} (f : α → R) := 
  {x : (Π i : α, localization.loc R (powers $ f i)) // ∀ j k : α, localise_more_left (f j) (f k) (x j) = localise_more_right (f j) (f k) (x k) } 

-- a theorem says that this is a subring.

definition structure_sheaf (R : Type u) [comm_ring R] : {U : set (X R) // topological_space.is_open (Zariski R) U} → Type u :=
λ ⟨U,HU⟩, let exf := D_f_are_a_basis U HU in let fH := classical.some_spec exf in structure_sheaf_on_union (classical.some fH)

-- the pair consisting of Spec(R) and its structure sheaf are an affine scheme, although it is currently not even clear
-- from the definition that everything is well-defined (I choose a cover; I still didn't do the work to check that
-- the resulting ring is independent of choices (or even that it is a ring!)

-- Just begun to think about general schemes below.


-/
