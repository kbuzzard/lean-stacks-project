import tag009I -- presheaf of types on basis 
import tag009H -- stalk on basis 
import tag009J -- sheaf of types on basis 
import data.set.function

definition sheaf_on_basis.canonical_map {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB) {U : set X} (BU : U ∈ B) : 
  FB.F BU → Π x : X, x ∈ U → presheaf_on_basis_stalk FB x := λ s x Hx,⟦{U := U, BU := BU, Hx := Hx, s := s}⟧

theorem lemma_condition_star_sections {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB) {U : set X} (BU : U ∈ B) 
   : function.injective (sheaf_on_basis.canonical_map FB HF BU) 
   ∧ set.image (sheaf_on_basis.canonical_map FB HF BU) set.univ = 
     { s : Π x : X, x ∈ U → presheaf_on_basis_stalk FB x | 
       ∀ x : X, x ∈ U → (∃ (V : set X) (BV : V ∈ B) (Hx : x ∈ V) (sigma : FB.F BV), 
         ∀ (y : X) (Hy : y ∈ U) (Hy' : y ∈ V), s y Hy = ⟦{U := V, BU := BV, Hx := Hy', s := sigma}⟧)} :=
sorry
