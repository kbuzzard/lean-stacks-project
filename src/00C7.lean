/-
 if R is a ring and if the multiplicative subset S consists completely of nonzerodivisors, then R→S−1R is injective

[proof omitted]
-/

import localization

universe u

variables {α : Type u} [comm_ring α] (S : set α) [is_submonoid α S]

theorem localization.inj_of_subset_non_zero_divisors (H : S ⊆ localization.non_zero_divisors α) :
  function.injective (localization.of_comm_ring α S) :=
λ x y h, let ⟨w, hws, hw⟩ := quotient.exact h in
eq.symm $ by simpa [add_neg_eq_zero] using H hws _ hw