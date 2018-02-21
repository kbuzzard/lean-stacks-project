/-
Lemma 10.16.6. Let R be a ring. Let f∈R. The map R→Rf induces via the functoriality of Spec a homeomorphism
Spec(Rf)⟶D(f)⊂Spec(R).
The inverse is given by 𝔭↦𝔭⋅Rf.

Proof. This is a special case of Lemma 10.16.5 (=tag 00E3)
-/

import analysis.topology.topological_space analysis.topology.continuity tag00E2 localization
import Kenny_comm_alg.Zariski

#check Zariski.induced 

/-- tag 00E4 -/

def topological_space.open_immersion {X Y : Type} [tX : topological_space X] [tY : topological_space Y] (φ : X → Y) := 
  continuous φ ∧ 
  function.injective φ ∧ 
  tY.is_open (set.image φ set.univ) ∧ 
  ∀ U : set X, tX.is_open U → tY.is_open (set.image φ U)

lemma lemma_standard_open (R : Type) [comm_ring R] (f : R) : 
  let φ := Zariski.induced $ localization.of_comm_ring R (powers f) in
    topological_space.open_immersion φ ∧ set.image φ set.univ = Spec.D'(f) := sorry

  
