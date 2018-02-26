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

set_option pp.notation false
def nonzero_on_U_is_mult_set {R : Type u} [comm_ring R] (U : set (X R)) : is_submonoid R {g : R | U ⊆ Spec.D'(g)} := 
{ one_mem := λ P HP, show P.val 1 → false,by simp, -- dammit P is a prime ideal of course it doens't contain 1
  mul_mem := begin
    intros f g Hf Hg,
    show U ⊆ Spec.D'(f*g),
    rw [tag00E0.lemma15 R f g],
    exact set.subset_inter Hf Hg
    end

}
  --sorry -- follows from lemma15 00E0
def zariski.structure_sheaf_standard {R : Type u} [comm_ring R] (U : set (X R)) (H : is_zariski.standard_open U) : Type u := 
  @localization.loc R _ {g : R | U ⊆ Spec.D'(g)} (nonzero_on_U_is_mult_set U)

lemma zariski.structure_sheaf_on_standard {R : Type u} [comm_ring R] (f : R) : let U := Spec.D'(f) in
  zariski.structure_sheaf_standard U (⟨f,rfl⟩) = localization.loc R (powers f) := sorry -- they are supposed to be canonically isomorphic not equal
  
