/-
This is a section.
It contains 00DZ, 00E0, 00E1 and 00E2 and 00E3 and 00E4 and 00E5 and 00E6 and 00E7 and 00E8 and 04PM

It also contains the following useful claim, just under Lemma 10.16.2 (tag 00E0):

The sets D(f) are open and form a basis for this topology (on Spec(R))

-/

import Kenny_comm_alg.temp analysis.topology.topological_space Kenny_comm_alg.Zariski

universe u 
variables α : Type u
variable t : topological_space α 
#check t 
#print topological_space 

def topological_space.is_topological_basis' {α : Type u} [t : topological_space α] (s : set (set α)) :=
(∀ U : set α, U ∈ s → t.is_open U) ∧ 
(∀ U : set α, t.is_open U → (∀ x, x ∈ U → ∃ V : set α, V ∈ s ∧ x ∈ V ∧ V ⊆ U))

-- this is what a basis should be, I think.

lemma D_f_form_basis (R : Type) [comm_ring R] : 
  topological_space.is_topological_basis {U : set (X R) | ∃ f : R, U = Spec.D'(f)} := 
begin
unfold topological_space.is_topological_basis,
split,
intros U HU,
cases HU with f Hf,
intros V HV,
admit,admit, -- unfinished as I was distracted by basis
end
