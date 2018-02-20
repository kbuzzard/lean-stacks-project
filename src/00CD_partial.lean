/-
if R is a ring, I and ideal of R and S a multiplicative subset of R, then S−1I is an ideal of S−1R, and we have S−1R/S−1I=S⎯⎯⎯−1(R/I), where S⎯⎯⎯ is the image of S in R/I, 

[proof omitted]
-/

import localization algebra.linear_algebra.quotient_module

universe u

variables {α : Type u} [comm_ring α] (S : set α) [is_submonoid α S]

variables (I : set α) [is_submodule I]

def localization.is_submodule.of_comm_ring :
  is_submodule {y : localization.loc α S | ∃ (x s : α) (hx : x ∈ I) (hs : s ∈ S), ⟦(⟨x, s, hs⟩:α × S)⟧ = y} :=
{ zero_ := ⟨(0:α), (1:α), @is_submodule.zero _ _ _ _ I _, is_submonoid.one_mem S, quotient.sound $ setoid.refl _⟩,
  add_  := λ m₁ m₂ ⟨x₁, s₁, hx₁, hs₁, h₁⟩ ⟨x₂, s₂, hx₂, hs₂, h₂⟩,
    ⟨s₁ * x₂ + s₂ * x₁, s₁ * s₂, is_submodule.add (is_submodule.smul _ hx₂) (is_submodule.smul _ hx₁),
     is_submonoid.mul_mem hs₁ hs₂, by rw [← h₁, ← h₂]; refl⟩,
  smul  := λ c m ⟨x, s, hx, hs, h⟩, quotient.induction_on c $ λ ⟨cr, cs, ch⟩,
    ⟨cr * x, cs * s, is_submodule.smul _ hx, is_submonoid.mul_mem ch hs, by rw [← h]; refl⟩ }

-- to be continued