/- Under defintion 25.5.2 (tag 01HT) and before 25.5.3 (01HU) there is an
argument which defines the sheaf of rings on Spec(R), and also the
quasicoherent sheaf
of O_X-modules attached to an R-module.
-/

/- Let's just do this for rings at this point.

-/
import Kenny_comm_alg.Zariski localization tag00E0
universe u

#check tag00E0.lemma15
#print is_prime_ideal

def is_zariski.standard_open {R : Type u} [comm_ring R] (U : set (X R)) := ∃ f : R, U = Spec.D'(f)

def nonzero_on_U_is_mult_set {R : Type u} [comm_ring R] (U : set (X R)) : is_submonoid R {g : R | U ⊆ Spec.D'(g)} := 
{ one_mem := λ P HP, @is_proper_ideal.one_not_mem _ _ P.1 P.2.1,
  mul_mem := begin
    intros f g Hf Hg,
    show U ⊆ Spec.D'(f*g),
    rw [tag00E0.lemma15 R f g],
    exact set.subset_inter Hf Hg
    end
}

def zariski.structure_sheaf_standard {R : Type u} [comm_ring R] (U : set (X R)) (H : is_zariski.standard_open U) : Type u := 
  @localization.loc R _ {g : R | U ⊆ Spec.D'(g)} (nonzero_on_U_is_mult_set U)

lemma zariski.structure_sheaf_on_standard {R : Type u} [comm_ring R] (f : R) : let U := Spec.D'(f) in
  zariski.structure_sheaf_standard U (⟨f,rfl⟩) = localization.loc R (powers f) := sorry
   -- they are supposed to be canonically isomorphic not equal
-- Ideas: The map goes from loc R (powers f) to loc R S (S the big set) because f is in S
-- so existence of the map is some universal property
-- Uniqueness is probably easy -- we know where R goes and where 1/f goes and that's all we need
-- Isomorphism seems harder. I want to write down an inverse using choice; have to go back to definition of S
-- to see 1/s in R[1/f] and that will be an inverse again because there's a unique R-algebra map.

