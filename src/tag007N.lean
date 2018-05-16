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

import tag009H -- to get definition of stalk, which is the only filtered colimit I care about right now
import tag009P -- presheaf of (commutative) rings on basis 
universe u 

theorem stalks_of_presheaf_of_rings_on_basis_are_rings {X : Type u} [topological_space X] {B : set (set X)}
{HB : topological_space.is_topological_basis B} (FPRB : presheaf_of_rings_on_basis HB) (x : X) :
comm_ring (presheaf_on_basis_stalk (FPRB.to_presheaf_of_types_on_basis) x) := sorry 
