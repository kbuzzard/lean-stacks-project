import Kenny_comm_alg.ideal_operations order.complete_lattice

universe u

variables {α : Type u} [comm_ring α]

namespace is_ideal

instance : lattice.complete_lattice {S : set α // is_ideal S} :=
{ sup          := λ S₁ S₂, ⟨is_ideal.add_ideal S₁.1 S₂.1, @@is_ideal.add.is_ideal _ S₁.2 S₂.2⟩,
  le_sup_left  := λ S₁ S₂, @is_ideal.subset_add_left _ _ S₁.1 S₂.1 S₁.2 S₂.2,
  le_sup_right := λ S₁ S₂, @is_ideal.subset_add_right _ _ S₁.1 S₂.1 S₁.2 S₂.2,
  sup_le       := λ S₁ S₂ S₃ h13 h23 x ⟨y, z, hy, hz, hx⟩, by rw hx; exact @@is_ideal.add _ S₃.2 (h13 hy) (h23 hz),

  inf          := λ S₁ S₂, ⟨S₁.1 ∩ S₂.1, @@is_ideal.inter.is_ideal _ S₁.2 S₂.2⟩,
  inf_le_left  := λ S₁ S₂, set.inter_subset_left S₁.1 S₂.1,
  inf_le_right := λ S₁ S₂, set.inter_subset_right S₁.1 S₂.1,
  le_inf       := λ S₁ S₂ S₃ h13 h23 x hx, ⟨h13 hx, h23 hx⟩,

  top := ⟨set.univ, is_ideal.univ⟩,
  le_top := λ x z hz, set.mem_univ z,

  bot := ⟨{0}, is_ideal.single_zero⟩,
  bot_le := λ x z hz, by simp at hz; rw hz; simp [@@is_ideal.zero _ x.1 x.2],

  Sup := λ SS, ⟨span {x | ∃ S:{S // is_ideal S}, S ∈ SS ∧ x ∈ S.val}, is_ideal_span⟩,
  le_Sup := λ SS x hx, subset_span_of_subset $ λ z hz, ⟨x, hx, hz⟩,
  Sup_le := λ SS x hx, span_minimal x.2.to_is_submodule $ λ z ⟨S, hs, hz⟩, hx S hs hz,

  Inf := λ SS, ⟨{x | ∀ S:{S : set α // is_ideal S}, S ∈ SS → x ∈ S.val}, sInter'.is_ideal SS⟩,
  Inf_le := λ SS x hx z hz, hz x hx,
  le_Inf := λ SS x hx z hz S hs, hx S hs hz,
  .. subrel.partial_order }

end is_ideal