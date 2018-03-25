import tag009J 

definition finite_cover_sheaf_property 
  {X : Type*} [T : topological_space X] 
  (B : set (set X)) 
  (HB : topological_space.is_topological_basis B)
  (FPTB : presheaf_of_types_on_basis HB)
  (Hstandard : ∀ {U V : set X}, B U → B V → B (U ∩ V))
  (U : set X)
  (BU : B U)
  (γ : Type*)
  (Hfingamma: fintype γ) -- only interested in finite covers here
  (Ui : γ → set X)
  (BUi : ∀ i : γ, B (Ui i))
  (Hcover: U = ⋃ (i : γ), (Ui i)) : 
  ∀ si : Π (i : γ), FPTB.F (BUi i), 
  (∀ i j : γ, FPTB.res (BUi i) (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_left _ _) (si i) = 
              FPTB.res (BUi j) (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_right _ _) (si j))
  → ∃! s : FPTB.F BU, ∀ i : γ, FPTB.res BU (BUi i) (_) s = si i 

theorem lemma_cofinal_systems_coverings_standard_case 
  {X : Type*} [T : topological_space X] 
  (B : set (set X)) 
  (HB : topological_space.is_topological_basis B)
  (FPTB : presheaf_of_types_on_basis HB)
  (Hstandard : ∀ U V : set X, B U → B V → B (U ∩ V))
  -- cofinal system is finite covers
  : 