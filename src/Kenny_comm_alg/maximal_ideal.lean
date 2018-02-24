import Kenny_comm_alg.ideal_lattice

noncomputable theory
local attribute [instance] classical.prop_decidable

universe u

class zero_ne_one' (α : Type u) [comm_ring α] : Prop :=
(zero_ne_one : (0:α) ≠ 1)

namespace is_ideal

section maximal_ideal

parameters {α : Type u} [comm_ring α] [zero_ne_one' α]

instance : partial_order {S : set α // is_proper_ideal S} :=
subrel.partial_order

instance : inhabited {S : set α // is_proper_ideal S} :=
⟨⟨{0},
  { ne_univ := λ h, zero_ne_one'.zero_ne_one α $
      have (1:α) ∈ (set.univ:set α) := trivial,
        by symmetry; rw ← h at this; simpa using this,
    .. is_ideal.single_zero }⟩⟩

theorem find_maximal_ideal_aux :
  ∃ (M : {S : set α // is_proper_ideal S}), ∀ x, M ≤ x → x = M :=
zorn.zorn' {S : set α // is_proper_ideal S} $
λ c x hx hc, ⟨⟨{y | ∃ S : {S : set α // is_proper_ideal S}, S ∈ c ∧ y ∈ S.val},
  { zero_ := ⟨x, hx, @@is_ideal.zero _ x.1 x.2.to_is_ideal⟩,
    add_  := λ x y ⟨Sx, hxc, hx⟩ ⟨Sy, hyc, hy⟩,
      or.cases_on (hc Sx Sy hxc hyc)
        (λ hxy, ⟨Sy, hyc, @@is_ideal.add _ Sy.2.to_is_ideal (hxy hx) hy⟩)
        (λ hyx, ⟨Sx, hxc, @@is_ideal.add _ Sx.2.to_is_ideal hx (hyx hy)⟩),
    smul  := λ x y ⟨Sy, hyc, hy⟩,
      ⟨Sy, hyc, @@is_ideal.mul_left _ Sy.2.to_is_ideal hy⟩,
    ne_univ := λ h, by rw set.eq_univ_iff_forall at h;
      rcases h 1 with ⟨S, hsc, hs⟩; apply S.2.ne_univ;
      exact @@is_submodule.univ_of_one_mem _ S.1
        S.2.to_is_ideal.to_is_submodule hs }⟩,
λ S hsc z hzs, ⟨S, hsc, hzs⟩⟩

def find_maximal_ideal : set α :=
(classical.some find_maximal_ideal_aux).1

instance find_maximal_ideal.is_maximal_ideal :
  is_maximal_ideal find_maximal_ideal :=
{ eq_or_univ_of_subset := λ T ht hmt, or_iff_not_imp_right.2 $
    λ h, congr_arg subtype.val $
    classical.some_spec find_maximal_ideal_aux
    ⟨T, { ne_univ := h, .. ht }⟩ hmt,
  ..(classical.some find_maximal_ideal_aux).2 }

end maximal_ideal

end is_ideal