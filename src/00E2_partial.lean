/-
Lemma 10.16.4. Suppose that φ:R→R′ is a ring homomorphism. The induced map
Spec(φ):Spec(R′)⟶Spec(R),𝔭′⟼φ−1(𝔭′)
is continuous for the Zariski topologies. In fact, for any element f∈R we have Spec(φ)−1(D(f))=D(φ(f)).

Proof. It is tag 00BV that 𝔭:=φ−1(𝔭′) is indeed a prime ideal of R. The last assertion of the lemma follows directly from the definitions, and implies the first. 
-/

import Kenny_comm_alg.Zariski analysis.topology.continuity

universes u v

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_ring_hom f]

def Zariski.induced : X β → X α :=
λ p, ⟨f ⁻¹' p.1, @@is_prime_ideal.hom_preimage _ _ f _ p.1 p.2⟩

instance que := Zariski α

theorem Zariski.induced.continuous : continuous (Zariski.induced f) :=
λ A ⟨E, ha⟩, ⟨f '' E, set.ext $ λ z,
begin
  split,
  { intros h hz,
    simp [Spec.V] at h,
    simp [set.mem_preimage_eq] at hz,
    simp [Zariski.induced] at hz,
    suffices : (⟨f ⁻¹' z.val, _⟩ : X α) ∈ Spec.V α E,
    { rw ha at this,
      exact this hz },
    simp [Spec.V],
    intros x hx,
    specialize @h (f x) ⟨x, hx, rfl⟩,
    exact h },
  { intros h x hz,
    rcases hz with ⟨w, H, hw⟩,
    rw ← hw,
    simp [Zariski.induced] at h,
    rw ← set.mem_compl_iff at h,
    rw ← ha at h,
    simp [Spec.V] at h,
    exact h H }
end⟩

-- to be continued