/- I am only interested in commutative rings here.
 The claim in part 5 of this tag (see https://stacks.math.columbia.edu/tag/007M for the definitions) implies
 that the category of commutative rings has filtered colimits which commute with the forgetful functor
 to set. I only need this in the special case that my limit is the stalk of a presheaf of rings.
 So I allow myself an import of a later tag, out of laziness, rather than formulating the statement 
 for some arbitrary colimit.
 -/

 /- Maybe in the future this file would contain a proof that a filtered colimit of commutative
 rings is a commutative ring.
 -/

/-
import tag009H -- to get definition of stalk, which is the only filtered colimit I care about right now
import tag009P -- presheaf of (commutative) rings on basis 
universe u 

theorem stalks_of_presheaf_of_rings_on_basis_are_rings {X : Type u} [topological_space X] {B : set (set X)}
{HB : topological_space.is_topological_basis B} (FPRB : presheaf_of_rings_on_basis HB) (x : X) :
comm_ring (presheaf_on_basis_stalk (FPRB.to_presheaf_of_types_on_basis) x) := {
  add := λ x y,begin end,
  add_assoc := sorry,
  zero := sorry,
  zero_add := sorry,
  add_zero := sorry,
  neg := sorry,
  add_left_neg := sorry,
  add_comm := sorry,
  mul := sorry,
  mul_assoc := sorry,
  mul_one := sorry,
  one := sorry,
  one_mul := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  mul_comm := sorry
}
-/

-- I can't face doing this. Let's do it properly
import Kenny_comm_alg.direct_limit
universe u 
namespace topological_space
variables {X : Type u} [topological_space X] {B : set (set X)}

definition basis_nhds (HB : topological_space.is_topological_basis B) (x : X) := {U : set X // x ∈ U ∧ U ∈ B} 

noncomputable instance basis_nhds_has_so_called_sup (HB : topological_space.is_topological_basis B) (x : X) :
lattice.has_sup (basis_nhds HB x) := {
  sup := λ Us Vs, begin
    cases (classical.indefinite_description _ (HB.1 Us.1 Us.2.2 Vs.1 Vs.2.2 x ⟨Us.2.1,Vs.2.1⟩))
      with W HW,
    cases (classical.indefinite_description _ HW) with HB HW,
    exact ⟨W,⟨HW.1,HB⟩⟩
  end 
}

instance basis_nhds_is_partial_order (HB : topological_space.is_topological_basis B) (x : X) :
partial_order (basis_nhds HB x) := 
{ le := λ Us Vs,Us.1 ⊆ Vs.1,
  le_refl := λ Us, set.subset.refl Us.1,
  le_trans := λ Us Vs Ws, set.subset.trans,
--  le_antisymm := λ Us Vs HUV HVU, subtype.eq (set.subset.antisymm HUV HVU)
  le_antisymm := λ Us Vs HUV HVU, subtype.eq $ set.subset.antisymm HUV HVU
--  le_antisymm := λ Us Vs, subtype.eq $ set.subset.antisymm
}

#check subtype

noncomputable theorem basis_nhds_are_directed_set {X : Type u} [topological_space X] {B : set (set X)} (HB : topological_space.is_topological_basis B)
(x : X) : directed_order (basis_nhds HB x) :=
{ le_sup_left := begin end,
  le_sup_right := sorry
}

end topological_space 