import analysis.topology.topological_space data.set 
import Kenny_comm_alg.Zariski
import Kenny_comm_alg.temp
import tag00EJ_statement
import localization

universes u v 

structure ring_morphism {α : Type*} {β : Type*} [Ra : comm_ring α] [Rb : comm_ring β] (f : α → β) :=
(f_zero : f 0 = 0)
(f_one : f 1 = 1)
(f_add : ∀ {a₁ a₂ : α}, f (a₁ + a₂) = f a₁ + f a₂)
(f_mul : ∀ {a₁ a₂ : α}, f (a₁ * a₂) = f a₁ * f a₂) 

local attribute [class] topological_space.is_open 

structure presheaf_of_rings (α : Type*) [T : topological_space α] 
  (F : Π U : set α, T.is_open U → Type*) :=
(Fring : ∀ U O, comm_ring (F U O))
(res : ∀ (U V : set α) [OU : T.is_open U] [OV : T.is_open V] (H : V ⊆ U), 
  (F U OU) → (F V OV))
(res_is_ring_morphism : ∀ (U V : set α) [OU : T.is_open U] [OV : T.is_open V] (H : V ⊆ U),
is_ring_hom (res U V H))
(Hid : ∀ (U : set α) [OU : T.is_open U], (res U U (set.subset.refl _)) = id)  
(Hcomp : ∀ (U V W : set α) [OU : T.is_open U] [OV : T.is_open V] [OW : T.is_open W]
  (HUV : V ⊆ U) (HVW : W ⊆ V),
  (res U W (set.subset.trans HVW HUV)) = (res V W HVW) ∘ (res U V HUV) )

attribute [class] presheaf_of_rings
--attribute [instance] presheaf_of_rings.Fring
--local attribute [instance] topological_space.is_open_inter

def res_to_inter_left {α : Type*} [T : topological_space α] 
  (F : Π U : set α, T.is_open U → Type*)
  [FP : presheaf_of_rings α F]
  (U V : set α) [OU : T.is_open U] [OV : T.is_open V] 
  : (F U OU) → (F (U ∩ V) (T.is_open_inter U V OU OV)) 
  := @presheaf_of_rings.res α _ _ FP U (U ∩ V) _ (T.is_open_inter U V OU OV) (set.inter_subset_left U V)

def res_to_inter_right {α : Type*} [T : topological_space α]
  (F : Π U : set α, T.is_open U → Type)
  [FP : presheaf_of_rings α F]
  (U V : set α) [OU : T.is_open U] [OV : T.is_open V]
  : (F V OV) → (F (U ∩ V) (T.is_open_inter U V OU OV)) 
  := @presheaf_of_rings.res α _ _ FP V (U ∩ V) _ (T.is_open_inter U V OU OV) (set.inter_subset_right U V)

def gluing {α : Type*} [T : topological_space α] (F : Π U : set α, T.is_open U → Type*) 
  [FP : presheaf_of_rings α F]
  (U :  set α)
  [UO : T.is_open U]
  {γ : Type*} (Ui : γ → set α)
  [UiO : ∀ i : γ, T.is_open (Ui i)]
  (Hcov : (⋃ (x : γ), (Ui x)) = U) 
  : (F U UO) → 
    {a : (Π (x : γ), (F (Ui x) (UiO x))) | ∀ (x y : γ), 
      (res_to_inter_left F (Ui x) (Ui y)) (a x) = 
      (res_to_inter_right F (Ui x) (Ui y)) (a y)} :=
λ r,⟨λ x,(FP.res U (Ui x) (Hcov ▸ set.subset_Union Ui x) r),
  λ x₁ y₁,
  have Hopen : T.is_open ((Ui x₁) ∩ (Ui y₁)) := (T.is_open_inter _ _ (UiO x₁) (UiO y₁)),
show ((@presheaf_of_rings.res _ _ _ FP (Ui x₁) ((Ui x₁) ∩ (Ui y₁)) _ Hopen _) ∘ 
      (@presheaf_of_rings.res _ _ _ FP U (Ui x₁) _ _ _)) r =
    ((@presheaf_of_rings.res _ _ _ FP (Ui y₁) ((Ui x₁) ∩ (Ui y₁)) _ Hopen _) ∘ 
      (@presheaf_of_rings.res _ _ _ FP U (Ui y₁) _ _ _)) r,by rw [←presheaf_of_rings.Hcomp,←presheaf_of_rings.Hcomp]⟩

structure sheaf_of_rings (α : Type*) [T : topological_space α] 
  (F : Π U : set α, T.is_open U → Type*) :=

(FP : presheaf_of_rings α F)
(Fsheaf : ∀ (U : set α) [OU : T.is_open U] 
          {γ : Type*} (Ui : γ → set α)
          [UiO : ∀ x : γ, T.is_open (Ui x)] 
          (Hcov : (⋃ (x : γ), (Ui x)) = U),
        function.bijective (gluing F U Ui Hcov)
)

--theorem D_f_are_a_basis {R : Type u} [comm_ring R] : ∀ U : set (X R), topological_space.is_open (Zariski R) U → ∃ α : Type v, ∃ f : α → R, U = set.Union (Spec.D' ∘ f) := sorry

--definition structure_sheaf_on_union {R : Type u} [comm_ring R] {α : Type} (f : α → R) := 
--  {x : (Π i : α, localization.loc R (powers $ f i)) // ∀ j k : α, localise_more_left (f j) (f k) (x j) = localise_more_right (f j) (f k) (x k) } 

--#check topological_space.is_open 
--#check @localization.at_prime
#check @sheaf_of_rings 


definition canonical_map {R : Type*} [comm_ring R] (g : R) (u : X R) (H : u ∈ Spec.D' g) 
: localization.away g → @localization.at_prime R _ u.val u.property 
:= sorry 


definition underlying_set_of_sheaf_of_rings_on_affine_scheme (R : Type*) [comm_ring R] 
: Π U : set (X R), topological_space.is_open (Zariski R) U → Type* 
:= λ U HU, { f : Π P : {u : X R // U u}, @localization.at_prime R _ P.val.val P.val.property // 
  ∀ u : X R, U u → ∃ g : R, Π H : u ∈ Spec.D' g, Π H2 : Spec.D' g ⊆ U, ∃ r : localization.away g, ∀ v : {v : X R // Spec.D' g v},
  f ⟨v.val, H2 (v.property)⟩ = canonical_map g v v.property r
   }

definition structure_sheaf_on_affine_scheme (R : Type*) [comm_ring R] : @sheaf_of_rings (X R) _ (underlying_set_of_sheaf_of_rings_on_affine_scheme R)
:= {
  FP := {
    Fring := sorry,
    res := sorry,
    res_is_ring_morphism := sorry,
    Hid := sorry,
    Hcomp := sorry,
  },
  Fsheaf := sorry
}

structure scheme :=
(α : Type u)
(T :topological_space α)
(O_X : {U : set α // T.is_open U} → Type v)
(O_X_sheaf_of_rings : sheaf_of_rings O_X) -- TODO
(locally_affine : ∃ β : Type v, ∃ cov : β → {U : set α // T.is_open U}, 
  set.Union (λ b, (cov b).val) = set.univ ∧
  ∀ b : β, ∃ R : Type w, comm_ring R ∧ true)


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
