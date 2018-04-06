import tag009J 
universes u v w uu vv ww uuu vvv www 

definition sheaf_property 
  {X : Type u} [T : topological_space X] 
  {B : set (set X)} 
  (HB : topological_space.is_topological_basis B)
  (FPTB : presheaf_of_types_on_basis HB)
  (Hstandard : ∀ {U V : set X}, B U → B V → B (U ∩ V))
  (U : set X)
  (BU : B U)
  (γ : Type u)
  --(Hfingamma: fintype γ) -- only interested in finite covers here
  (Ui : γ → set X)
  (BUi : ∀ i : γ, B (Ui i))
  (Hcover: (⋃ (i : γ), (Ui i)) = U) : Prop := 
  ∀ si : Π (i : γ), FPTB.F (BUi i), 
  (∀ i j : γ, FPTB.res (BUi i) (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_left _ _) (si i) = 
              FPTB.res (BUi j) (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_right _ _) (si j))
  → ∃! s : FPTB.F BU, ∀ i : γ, FPTB.res BU (BUi i) (Hcover ▸ (set.subset_Union Ui i)) s = si i 

definition basis_is_compact 
  {X : Type u} [T : topological_space X] 
  {B : set (set X)} 
  (HB : topological_space.is_topological_basis B) : Prop :=
  ∀ U : set X, B U →
    ∀ β : Type u, ∀ Ui : β → set X,
    (∀ i : β, B (Ui i)) → 
    (⋃ (i : β), Ui i) = U →
    ∃ γ : Type u, ∃ Hfinite : fintype γ,
    ∃ f : γ → β, 
    (⋃ (j : γ), Ui (f j)) = U 

theorem lemma_cofinal_systems_coverings_standard_case 
  {X : Type u} [T : topological_space X] 
  {B : set (set X)} 
  (HB : topological_space.is_topological_basis B)
  (FPTB : presheaf_of_types_on_basis HB)
  (Hstandard : ∀ U V : set X, B U → B V → B (U ∩ V))
  -- cofinal system is finite covers
  (HBcompact: basis_is_compact HB)
  : 
  (∀ U : set X, ∀ BU : B U,
  ∀ γ : Type u, fintype γ → -- note fintype here
  ∀ Ui : γ → set X,
  ∀ BUi :  ∀ i : γ, B (Ui i),
  ∀ Hcover: (⋃ (i : γ), (Ui i)) = U,
  sheaf_property HB FPTB Hstandard U BU γ Ui BUi Hcover)
  → 
  (∀ U : set X, ∀ BU : B U,
  ∀ γ : Type u, 
  ∀ Ui : γ → set X,
  ∀ BUi :  ∀ i : γ, B (Ui i),
  ∀ Hcover: (⋃ (i : γ), (Ui i)) = U,  
  sheaf_property HB FPTB Hstandard U BU γ Ui BUi Hcover)
  := 
begin
  intro Hfinite,
  intros U BU β Ui BUi Hcover,
  intros si Hsiglue,
  -- Hcover has a finite subcover
  cases HBcompact U BU β Ui BUi Hcover with γ Hγ,
  cases Hγ with HFinγ Hf,
  cases Hf with f Hfincover,
  have X := Hfinite U BU γ HFinγ (Ui ∘ f) (λ j, BUi (f j)) Hfincover,
  
  admit,
end


  -- the **only property of fintype you will need here**
  -- is basis_is_compact; you definitely do not need
  -- the fact that a fintype is finite -- I could replace
  -- fintype with some arbitrary typeclass here, as long
  -- as I replace it in both the theorem and the definition.

  -- What I am trying to stress is that this is not an assertion
  -- about compactness or finite covers, the correct theorem
  -- is that if the sheaf axiom holds on a "cofinite collection
  -- of covers" then it holds for all covers. I didn't have time
  -- to formalise "cofinite collection of covers" so I just
  -- formalised "finite covers" and put it as an
  -- axiom that every element of B is compact. Think of the
  -- compactness assumption HBcompact as saying that every
  -- cover can be refined to a "special" cover, and that
  -- if the sheaf axiom is true for "special" covers then
  -- it's true for all covers.
