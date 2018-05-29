import analysis.topology.topological_space scheme

set_option pp.proofs true 

theorem presheaves_iso (X : Type) [H : topological_space X] (F : presheaf_of_types X) : 
are_isomorphic_presheaves_of_types
    (presheaf_of_types_pullback_under_open_immersion F id 
      (topological_space.open_immersion_id _))
    F
:= 
begin 
  constructor,tactic.swap,
  { constructor,tactic.swap,
    { intros U HU,
      have Hid := topological_space.open_immersion_id X, 
      -- goal now
      show (presheaf_of_types_pullback_under_open_immersion F id Hid).F HU → F.F HU,
      --unfold presheaf_of_types_pullback_under_open_immersion, -- fails
      show (F.F ((Hid.fopens U).mp HU)) → F.F HU, -- obtained by "#reduce" calculation below
      show (F.F (_ : is_open (id '' U)) → F.F HU), -- obtained by more out-of-proof unravelling

      sorry
    },sorry,
    
  },
  sorry
end 
variables 
(X : Type)
(H : topological_space X)
(F : presheaf_of_types X)
(U : set X)
(HU : topological_space.is_open H U)
(Hid : topological_space.open_immersion (@id X))

#reduce (presheaf_of_types_pullback_under_open_immersion F id Hid).F
-- λ (U : X → Prop) (HU : topological_space.is_open H U), F.F ((Hid.fopens U).mp HU)
#check (Hid.fopens U).mp -- is_open U → is_open (id '' U)


#exit 

/-
theorem presheaves_iso (R : Type) [comm_ring R] : 
are_isomorphic_presheaves_of_rings
    (presheaf_of_rings_pullback_under_open_immersion (zariski.structure_presheaf_of_rings R) id 
      (topological_space.open_immersion_id _))
    (zariski.structure_presheaf_of_rings R)
:= 
begin 
  constructor,tactic.swap,
  { constructor,tactic.swap,
    { constructor,tactic.swap,
        { intros U HU, 
          intro x,
          unfold presheaf_of_rings_pullback_under_open_immersion at x,
          dsimp at x,
          let y := (presheaf_of_types_pullback_under_open_immersion ((zariski.structure_presheaf_of_rings R).to_presheaf_of_types) id
     (topological_space.open_immersion_id (X R))).F
    HU,
    cases
        
          sorry,
        },
    sorry,
    },
    sorry,
  },
  sorry 
  end

#print presheaf_of_types_pullback_under_open_immersion 

--#print presheaf_of_types_pullback_under_open_immersion
#exit

          -- should I use res or id?
          change ((presheaf_of_rings_pullback_under_open_immersion (zariski.structure_presheaf_of_rings R) id
    _).to_presheaf_of_types).F HU at x,
        }
    }
  }
  


-- RES ATTEMPT IS HERE
            refine (zariski.structure_presheaf_of_rings R).res _ _ _ _ _,
              rwa set.image_id,
              rwa set.image_id,
          },
          intros U V HU HV Hsub,
          refl,
        },
        intros,constructor,
        {intros x y,refl,
        },
        { intros x y,refl,
        },
        { refl
        },
      },
    { existsi _,tactic.swap,
      { constructor,tactic.swap,
        { constructor,tactic.swap,
          { intros U HU, -- should I use res again??
            refine (zariski.structure_presheaf_of_rings R).res _ _ _ _ _,
              rwa set.image_id,
              rwa set.image_id,
          },
          intros U V HU HV Hsub,
          refl,
        },
        intros,constructor,
        {intros x y,refl,
        },
        { intros x y,refl,
        },
        { refl
        }
      },
    constructor,
    {
      unfold is_identity_morphism_of_presheaves_of_types,
      intros,
      funext,
      unfold composition_of_morphisms_of_presheaves_of_types,
      dsimp,
      show (zariski.structure_presheaf_of_types R).res U (id '' U) OU _ _
      ((zariski.structure_presheaf_of_types R).res (id '' U) U _ OU _ x) =
    x,
      rw ←presheaf_of_types.Hcomp',
      simp,
    },
    { unfold is_identity_morphism_of_presheaves_of_types,
      intros,
      funext,
      unfold composition_of_morphisms_of_presheaves_of_types,
      dsimp,
      show (zariski.structure_presheaf_of_types R).res (id '' U) U _ OU _
      ((zariski.structure_presheaf_of_types R).res U (id '' U) OU _ _ x) =
    x,
      rw ←presheaf_of_types.Hcomp',
      simp,
       
    },
  }
  end 




import algebra.ring 

structure pre_semi_sheaf_of_rings (α : Type) := 
(F : Π (U : set α), Type)
[Fring : ∀ (U : set α), comm_ring (F U)]

attribute [instance] pre_semi_sheaf_of_rings.Fring

structure morphism_of_pre_semi_sheaves_of_rings {α : Type}
  (FPT : pre_semi_sheaf_of_rings α) (GPT : pre_semi_sheaf_of_rings α) :=
(morphism : ∀ U : set α, (FPT.F U) → GPT.F U)
(ring_homs : ∀ U : set α, @is_ring_hom _ _ _ _ (morphism U))

attribute [instance]  morphism_of_pre_semi_sheaves_of_rings.ring_homs

def is_identity_morphism_of_pre_semi_sheaves_of_rings {α : Type}
  {FPT : pre_semi_sheaf_of_rings α} (phi: morphism_of_pre_semi_sheaves_of_rings FPT FPT) :=
  ∀ (U : set α), phi.morphism U = id

def composition_of_morphisms_of_pre_semi_sheaves_of_rings {α : Type}
  {FPT GPT HPT : pre_semi_sheaf_of_rings α} (fg : morphism_of_pre_semi_sheaves_of_rings FPT GPT)
  (gh : morphism_of_pre_semi_sheaves_of_rings GPT HPT) :
morphism_of_pre_semi_sheaves_of_rings FPT HPT :=
{ morphism := λ U, gh.morphism U ∘ fg.morphism U,
  ring_homs := λ U, is_ring_hom.comp _ _ -- composition of two ring homs is a ring hom done by type class inference
}


def are_isomorphic_pre_semi_sheaves_of_rings {α : Type}
  (FPR : pre_semi_sheaf_of_rings α) (GPR : pre_semi_sheaf_of_rings α) : Prop := 
∃ (fg : morphism_of_pre_semi_sheaves_of_rings FPR GPR) (gf : morphism_of_pre_semi_sheaves_of_rings GPR FPR),
  is_identity_morphism_of_pre_semi_sheaves_of_rings (composition_of_morphisms_of_pre_semi_sheaves_of_rings fg gf)
  ∧ is_identity_morphism_of_pre_semi_sheaves_of_rings (composition_of_morphisms_of_pre_semi_sheaves_of_rings gf fg)

definition pre_semi_sheaf_of_rings_pullback
  {α : Type}
  {β : Type}
  (PR : pre_semi_sheaf_of_rings β)
  (f : α → β)
  : pre_semi_sheaf_of_rings α :=
{ F := λ V,PR.F (f '' V)
}

theorem pre_semi_sheaves_iso (X : Type) (F : pre_semi_sheaf_of_rings X) : 
are_isomorphic_pre_semi_sheaves_of_rings
    (pre_semi_sheaf_of_rings_pullback F id) F
:= 
begin
  constructor,
  { constructor,tactic.swap,
    { constructor,tactic.swap,
      { intros U s,
        unfold pre_semi_sheaf_of_rings_pullback,
        suffices : F.F (id '' U), by simpa using this,
        have reluctant_to_use : id '' U = U := by rw set.image_id,
        rw reluctant_to_use,
        exact s,
      },
      intro U,
      simp,
      sorry
    },
    dsimp,split,
    sorry,
    sorry,
  },
  sorry,
end 

-/