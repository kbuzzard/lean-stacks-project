/- Under defintion 25.5.2 (tag 01HT) and before 25.5.3 (01HU) there is an
argument which defines the sheaf of rings on Spec(R), and also the
quasicoherent sheaf
of O_X-modules attached to an R-module.
-/

/- Let's just do this for rings at this point.

-/
import Kenny_comm_alg.Zariski localization
universe u

def is_zariski.standard_open {R : Type u} [comm_ring R] (U : set (X R)) := ∃ f : R, U = Spec.D'(f)

def nonzero_on_U_is_mult_set {R : Type u} [comm_ring R] (U : set (X R)) : is_submonoid {g : R | U ⊆ Spec.D'(g)} := sorry
def zariski.structure_sheaf_standard {R : Type u} [comm_ring R] (U : set (X R)) (H : is_zariski.standard_open U) : Type u := localization.loc R {g : R | U ⊆ Spec.D'(g)}
