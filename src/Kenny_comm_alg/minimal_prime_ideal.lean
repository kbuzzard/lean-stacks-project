import Kenny_comm_alg.ideal_lattice

noncomputable theory
local attribute [instance] classical.prop_decidable

universe u

namespace is_ideal

section minimal_prime_ideal

parameters {α : Type u} [comm_ring α]
parameters (I : set α) [hi : is_ideal I]
parameters (P : set α) [hp : is_prime_ideal P]
parameters (hip : I ⊆ P)
include hi hp hip

private theorem find_minimal_prime_ideal_aux :
  ∃ (M : {S // I ⊆ S ∧ S ⊆ P ∧ is_prime_ideal S}), ∀ x, x ≤ M → x = M :=
@@zorn.zorn' (order_dual {S // I ⊆ S ∧ S ⊆ P ∧ is_prime_ideal S})
_
⟨⟨P, hip, set.subset.refl P, hp⟩⟩ $
λ c x hxc hc, ⟨⟨{y | ∀ S : {S // I ⊆ S ∧ S ⊆ P ∧ is_prime_ideal S}, S ∈ c → y ∈ S.val},
  λ z hz S hsc, S.2.1 hz,
  λ z hz, x.2.2.1 $ hz x hxc,
  { zero_ := λ S hsc, @@is_ideal.zero _ S.1
      S.2.2.2.to_is_proper_ideal.to_is_ideal,
    add_ := λ x y hx hy S hsc, @@is_ideal.add _
      S.2.2.2.to_is_proper_ideal.to_is_ideal
      (hx S hsc) (hy S hsc),
    smul := λ x y hy S hsc, @@is_ideal.mul_left _
      S.2.2.2.to_is_proper_ideal.to_is_ideal
      (hy S hsc),
    ne_univ := λ h, @is_proper_ideal.ne_univ α _ x.1 x.2.2.2.1 $
      @is_submodule.univ_of_one_mem α _ x.1 x.2.2.2.1.1.1 $
      by rw set.eq_univ_iff_forall at h;
      exact h 1 x hxc,
    mem_or_mem_of_mul_mem := λ x y hxy,
      or_iff_not_and_not.2 $ λ ⟨hx, hy⟩,
      let ⟨Sx, hsx⟩ := not_forall.1 hx in
      let ⟨hxc, hxs⟩ := not_imp.1 hsx in
      let ⟨Sy, hsy⟩ := not_forall.1 hy in
      let ⟨hyc, hys⟩ := not_imp.1 hsy in
      or.cases_on (hc Sx Sy hxc hyc)
        (λ hSxy, hxs $ hSxy $ or.resolve_right
           (@@is_prime_ideal.mem_or_mem_of_mul_mem _ Sy.2.2.2 $ hxy Sy hyc)
           hys)
        (λ hSyx, hys $ hSyx $ or.resolve_left
           (@@is_prime_ideal.mem_or_mem_of_mul_mem _ Sx.2.2.2 $ hxy Sx hxc)
           hxs) }⟩,
λ S hsc z hz, hz S hsc⟩

def find_minimal_prime_ideal : set α :=
(classical.some find_minimal_prime_ideal_aux).1

theorem find_minimal_prime_ideal.ideal_contains : I ⊆ find_minimal_prime_ideal :=
(classical.some find_minimal_prime_ideal_aux).2.1

theorem find_minimal_prime_ideal.contains_prime : find_minimal_prime_ideal ⊆ P :=
(classical.some find_minimal_prime_ideal_aux).2.2.1

def find_minimal_prime_ideal.is_prime_ideal :
  is_prime_ideal find_minimal_prime_ideal :=
(classical.some find_minimal_prime_ideal_aux).2.2.2

def find_minimal_prime_ideal.minimal (S : set α) [hs : is_prime_ideal S]
  (his : I ⊆ S) (hsm : S ⊆ find_minimal_prime_ideal) :
  S = find_minimal_prime_ideal :=
congr_arg subtype.val $
classical.some_spec
  find_minimal_prime_ideal_aux
  ⟨S, his, set.subset.trans hsm find_minimal_prime_ideal.contains_prime, hs⟩ hsm

private theorem find_minimal_prime_ideal_aux' :
  ∃ (M : {S // I ⊆ S ∧ is_prime_ideal S}), ∀ x, x ≤ M → x = M :=
@@zorn.zorn' (order_dual {S // I ⊆ S ∧ is_prime_ideal S})
_
⟨⟨P, hip, hp⟩⟩ $
λ c x hxc hc, ⟨⟨{y | ∀ S : {S // I ⊆ S ∧ is_prime_ideal S}, S ∈ c → y ∈ S.val},
  λ z hz S hsc, S.2.1 hz,
  { zero_ := λ S hsc, @@is_ideal.zero _ S.1
      S.2.2.to_is_proper_ideal.to_is_ideal,
    add_ := λ x y hx hy S hsc, @@is_ideal.add _
      S.2.2.to_is_proper_ideal.to_is_ideal
      (hx S hsc) (hy S hsc),
    smul := λ x y hy S hsc, @@is_ideal.mul_left _
      S.2.2.to_is_proper_ideal.to_is_ideal
      (hy S hsc),
    ne_univ := λ h, @is_proper_ideal.ne_univ α _ x.1 x.2.2.1 $
      @is_submodule.univ_of_one_mem α _ x.1 x.2.2.1.1.1 $
      by rw set.eq_univ_iff_forall at h;
      exact h 1 x hxc,
    mem_or_mem_of_mul_mem := λ x y hxy,
      or_iff_not_and_not.2 $ λ ⟨hx, hy⟩,
      let ⟨Sx, hsx⟩ := not_forall.1 hx in
      let ⟨hxc, hxs⟩ := not_imp.1 hsx in
      let ⟨Sy, hsy⟩ := not_forall.1 hy in
      let ⟨hyc, hys⟩ := not_imp.1 hsy in
      or.cases_on (hc Sx Sy hxc hyc)
        (λ hSxy, hxs $ hSxy $ or.resolve_right
           (@@is_prime_ideal.mem_or_mem_of_mul_mem _ Sy.2.2 $ hxy Sy hyc)
           hys)
        (λ hSyx, hys $ hSyx $ or.resolve_left
           (@@is_prime_ideal.mem_or_mem_of_mul_mem _ Sx.2.2 $ hxy Sx hxc)
           hxs) }⟩,
λ S hsc z hz, hz S hsc⟩

def find_minimal_prime_ideal' : set α :=
(classical.some find_minimal_prime_ideal_aux').1

theorem find_minimal_prime_ideal'.ideal_contains : I ⊆ find_minimal_prime_ideal' :=
(classical.some find_minimal_prime_ideal_aux').2.1

def find_minimal_prime_ideal'.is_prime_ideal :
  is_prime_ideal find_minimal_prime_ideal' :=
(classical.some find_minimal_prime_ideal_aux').2.2

def find_minimal_prime_ideal'.minimal (S : set α) [hs : is_prime_ideal S]
  (his : I ⊆ S) (hsm : S ⊆ find_minimal_prime_ideal') :
  S = find_minimal_prime_ideal' :=
congr_arg subtype.val $
classical.some_spec
  find_minimal_prime_ideal_aux'
  ⟨S, his, hs⟩ hsm

end minimal_prime_ideal

end is_ideal