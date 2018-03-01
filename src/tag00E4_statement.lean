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
  ∀ U : set X, tX.is_open U → tY.is_open (set.image φ U)

lemma lemma_standard_open (R : Type) [comm_ring R] (f : R) : 
  let φ := Zariski.induced $ localization.of_comm_ring R (powers f) in
  topological_space.open_immersion φ ∧ φ '' set.univ = Spec.D'(f) :=
⟨⟨Zariski.induced.continuous _,
  λ x y hxy, subtype.eq $ set.ext $ λ z,
    quotient.induction_on z $ λ ⟨r, s, hs⟩,
    ⟨λ hr, have h1 : _ := localization.mul_denom R _ r s hs,
       have h2 : localization.of_comm_ring R (powers f) r ∈ x.val,
         from eq.rec (@@is_ideal.mul_right _ x.2.1.1 hr) h1,
       have h3 : r ∈ (Zariski.induced (localization.of_comm_ring R (powers f)) y).1,
         from eq.rec h2 hxy,
       have h4 : localization.of_comm_ring R (powers f) r ∈ y.val,
         from h3,
       have h5 : _ := localization.mul_inv_denom R _ r s hs,
       eq.rec (@@is_ideal.mul_right _ y.2.1.1 h4) h5,
     λ hr, have h1 : _ := localization.mul_denom R _ r s hs,
       have h2 : localization.of_comm_ring R (powers f) r ∈ y.val,
         from eq.rec (@@is_ideal.mul_right _ y.2.1.1 hr) h1,
       have h3 : r ∈ (Zariski.induced (localization.of_comm_ring R (powers f)) x).1,
         from eq.rec h2 hxy.symm,
       have h4 : localization.of_comm_ring R (powers f) r ∈ x.val,
         from h3,
       have h5 : _ := localization.mul_inv_denom R _ r s hs,
       eq.rec (@@is_ideal.mul_right _ x.2.1.1 h4) h5⟩,
  λ S hs, let ⟨F, hsf⟩ := hs in
    let F' := {r | ∃ (s ∈ powers f), ⟦(⟨r, s, H⟩ : R × powers f)⟧ ∈ F} in
    ⟨F', set.ext $ λ z,
     ⟨λ hz ⟨x, hxs, hnz⟩, have h1 : x ∈ Spec.V F,
        from λ g, quotient.induction_on g $ λ ⟨r, s, hsg⟩ hg,
          have h2 : r ∈ F', from ⟨_, hsg, hg⟩,
          have h3 : _, from hz h2,
          begin
            rw ← localization.mul_inv_denom,
            rw ← hnz at h3,
            exact @@is_ideal.mul_right _ x.2.1.1 h3
          end,
        by rw hsf at h1; exact h1 hxs,
      λ hz g ⟨t, ht, hgtf⟩, sorry⟩⟩⟩, --I'm lost
 set.ext $ λ x,
 ⟨λ ⟨y, _, hyx⟩ hfx, have h1 : localization.of_comm_ring R (powers f) f ∈ y.val,
    by rwa ← hyx at hfx,
    @@is_prime_ideal.one_not_mem _ y.1 y.2 $
    begin
      rw ← @localization.div_self _ _ (powers f) _ f ⟨1, by simp⟩,
      unfold localization.mk,
      rw ← localization.mul_inv_denom _ (powers f),
      exact @@is_ideal.mul_right _ y.2.1.1 h1
    end,
  λ hx, sorry⟩⟩