import tag009J 

definition sheaf_property 
  {X : Type*} [T : topological_space X] 
  {B : set (set X)} 
  (HB : topological_space.is_topological_basis B)
  (FPTB : presheaf_of_types_on_basis HB)
  (Hstandard : ∀ {U V : set X}, B U → B V → B (U ∩ V))
  (U : set X)
  (BU : B U)
  (γ : Type*)
  --(Hfingamma: fintype γ) -- only interested in finite covers here
  (Ui : γ → set X)
  (BUi : ∀ i : γ, B (Ui i))
  (Hcover: (⋃ (i : γ), (Ui i)) = U) : Prop := 
  ∀ si : Π (i : γ), FPTB.F (BUi i), 
  (∀ i j : γ, FPTB.res (BUi i) (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_left _ _) (si i) = 
              FPTB.res (BUi j) (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_right _ _) (si j))
  → ∃! s : FPTB.F BU, ∀ i : γ, FPTB.res BU (BUi i) (Hcover ▸ (set.subset_Union Ui i)) s = si i 

definition basis_is_compact 
  {X : Type*} [T : topological_space X] 
  {B : set (set X)} 
  (HB : topological_space.is_topological_basis B) : Prop :=
  ∀ U : set X, B U →
    ∀ β : Type*, ∀ Ui : β → set X,
    (∀ i : β, B (Ui i)) → 
    (⋃ (i : β), Ui i) = U →
    ∃ γ : Type*, ∃ Hfinite : fintype γ,
    ∃ f : γ → β, 
    (⋃ (j : γ), Ui (f j)) = U 


theorem lemma_cofinal_systems_coverings_standard_case 
  {X : Type*} [T : topological_space X] 
  {B : set (set X)} 
  (HB : topological_space.is_topological_basis B)
  (FPTB : presheaf_of_types_on_basis HB)
  (Hstandard : ∀ U V : set X, B U → B V → B (U ∩ V))
  -- cofinal system is finite covers
  (HBcompact: basis_is_compact HB)
  : 
  (∀ U : set X, ∀ BU : B U,
  ∀ γ : Type*, fintype γ → -- note fintype here
  ∀ Ui : γ → set X,
  ∀ BUi :  ∀ i : γ, B (Ui i),
  ∀ Hcover: (⋃ (i : γ), (Ui i)) = U,
  sheaf_property HB FPTB Hstandard U BU γ Ui BUi Hcover)
  → 
  (∀ U : set X, ∀ BU : B U,
  ∀ γ : Type*, 
  ∀ Ui : γ → set X,
  ∀ BUi :  ∀ i : γ, B (Ui i),
  ∀ Hcover: (⋃ (i : γ), (Ui i)) = U,  
  sheaf_property HB FPTB Hstandard U BU γ Ui BUi Hcover)
  := sorry 

  -- the **only property of fintype you will need here**
  -- is basis_is_compact; you definitely do not need
  -- the fact that a fintype is finite -- I coudl replace
  -- fintype with some arbitrary typeclass here, as long
  -- as I replace it in both the theorem and the definition.
  
