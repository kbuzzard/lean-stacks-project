import analysis.topology.topological_space
import tag009I 
-- Kevin and Kenny

-- union of a bunch of sets U_i = U implies each U_i subset of U
def helper1 {X : Type*} {γ : Type*} {U : set X} {Ui : γ → set X} {i : γ} :
(⋃ (i' : γ), (Ui i')) = U → Ui i ⊆ U := λ H z hz, H ▸ ⟨_, ⟨_, rfl⟩, hz⟩

-- union of a bunch of sets U_{ijk} = U_i intersect U_j implies U_{ijk} sub U_i
def helper2 {X : Type*} {γ : Type*}  {Ui : γ → set X}
{ β : γ → γ → Type*} {Uijk : Π (i j : γ), β i j → set X} {i j : γ} {k : β i j}
: (⋃ (k' : β i j), Uijk i j k') = Ui i ∩ Ui j → Uijk i j k ⊆ Ui i :=
λ H, have H1 : Uijk i j k ⊆ Ui i ∩ Ui j,
from λ z hz, H ▸ ⟨_, ⟨_, rfl⟩, hz⟩,
set.subset.trans H1 (set.inter_subset_left _ _)

-- union of a bunch of sets U_{ijk} = U_i intersect U_j implies U_{ijk} sub U_j
def helper3 {X : Type*} {γ : Type*} {Ui : γ → set X}
{ β : γ → γ → Type*} {Uijk : Π (i j : γ), β i j → set X} {i j : γ} {k : β i j}
: (⋃ (k' : β i j), Uijk i j k') = Ui i ∩ Ui j → Uijk i j k ⊆ Ui j :=
λ H, have H1 : Uijk i j k ⊆ Ui i ∩ Ui j,
from λ z hz, H ▸ ⟨_, ⟨_, rfl⟩, hz⟩,
set.subset.trans H1 (set.inter_subset_right _ _)

-- This is the correct definition of sheaf of types on a basis, with no assumption that
-- intersection of two basis elements is a basis element. Do we ever need it?
definition is_sheaf_of_types_on_basis {X : Type*} [T : topological_space X] 
  {B : set (set X)}
  {HB : topological_space.is_topological_basis B}
  (FPTB : presheaf_of_types_on_basis HB) : Prop :=
∀ {{U : set X}} (BU : B U) {γ : Type*} (Ui : γ → set X) (BUi : ∀ i : γ, B (Ui i))
  (Hcov : (⋃ (x : γ), (Ui x)) = U)
  { β : γ → γ → Type*} (Uijk : Π (i j : γ), β i j → set X)
  (BUijk : ∀ i j : γ, ∀ k : β i j, B (Uijk i j k) )
  (Hcov2 : ∀ i j : γ, (⋃ (k : β i j), Uijk i j k )= Ui i ∩ Ui j)
  (si : Π (i : γ), FPTB.F (BUi i))-- sections on the cover
  -- if they agree on overlaps
  (Hagree : ∀ i j : γ, ∀ k : β i j, 
    FPTB.res (BUi i) (BUijk i j k) (helper2 (Hcov2 i j): Uijk i j k ⊆ Ui i) (si i)
    = FPTB.res (BUi j) (BUijk i j k) (helper3 (Hcov2 i j) : Uijk i j k ⊆ Ui j) (si j)),
  -- then there's a unique global section which agrees with all of them.
  ∃! s : FPTB.F BU, ∀ i : γ, FPTB.res BU (BUi i) ((helper1 Hcov) : Ui i ⊆ U) s = si i
   
