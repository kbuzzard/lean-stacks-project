import analysis.topology.continuity
universe u 

namespace tactic
namespace interactive

open interactive interactive.types

meta def ccases (e : parse cases_arg_p) (ids : parse with_ident_list) :=
do cases (e.1,``(classical.indefinite_description _ %%(e.2))) ids

end interactive
end tactic

open topological_space

structure topological_space.open_immersion'
  {α : Type*} [Tα : topological_space α]
  {β : Type*} [Tβ : topological_space β]
  (f : α → β) : Prop :=
(fcont : continuous f)
(finj : function.injective f)
(fopens : ∀ U : set α, is_open U ↔ is_open (f '' U))

lemma topological_space.immersion_sends_opens_to_opens 
  {α : Type*} [Tα : topological_space α]
  {β : Type*} [Tβ : topological_space β]
  (f : α → β) (H : topological_space.open_immersion' f) : 
∀ U : set α, is_open U → is_open (f '' U) := λ U OU, (H.fopens U).1 OU

--#check compact
-- note compact_elim_finite_subcover and compact_of_finite_subcover


-- can I use ccases for this?
lemma topological_space.Union_basis_elements_of_open {α : Type u} [topological_space α]
{B : set (set α)} (HB : is_topological_basis B) {U : set α} (HU : is_open U) :
∃ (β : Type u) (f : β → set α), U = set.Union f ∧ ∀ i : β, f i ∈ B := 
begin
  let β := {x : α // x ∈ U},
  existsi β,
  have f0 := λ i : β, (mem_basis_subset_of_mem_open HB U i.property HU),
  let f := λ i, classical.some (f0 i),
  have f1 : ∀ (i : β), ∃ (H : (f i) ∈ B), (i.val ∈ (f i) ∧ (f i) ⊆ U) := λ i, classical.some_spec (f0 i),
  let g := λ i, classical.some (f1 i),
  have g1 : ∀ (i : β), (i.val ∈ f i ∧ f i ⊆ U) := λ i, classical.some_spec (f1 i),
  existsi f,
  split,
  { rw set.subset.antisymm_iff,
    split,
    { intros y Hy,
      let i : β := ⟨y,Hy⟩,
      existsi (f ⟨y,Hy⟩),
      constructor,
        existsi i,
        refl,
      exact (g1 i).left,
    },
    { intros y Hy,
      cases Hy with V HV,cases HV with HV Hy,cases HV with i Hi,
      apply (g1 i).2,
      rwa ←Hi,
    },
  },
  { intro i,
    exact g i
  }
end

-- here's Mario's better proof
/-
lemma sUnion_basis_elements_of_open {α : Type u} [topological_space α]
{B : set (set α)} (HB : is_topological_basis B) {U : set α} (HU : is_open U) :
∃ (S : set (set α)), U = ⋃₀ S ∧ S ⊆ B :=
⟨{b ∈ B | b ⊆ U}, set.ext (λ a,
   ⟨λ ha, let ⟨b, hb, ab, bu⟩ := mem_basis_subset_of_mem_open HB _ ha HU in
              ⟨b, ⟨hb, bu⟩, ab⟩,
    λ ⟨b, ⟨hb, bu⟩, ab⟩, bu ab⟩),
 λ b h, h.1⟩

lemma Union_basis_elements_of_open {α : Type u} [topological_space α]
{B : set (set α)} (HB : is_topological_basis B) {U : set α} (HU : is_open U) :
∃ (β : Type u) (f : β → set α), U = (⋃ i, f i) ∧ ∀ i : β, f i ∈ B :=
let ⟨S, su, sb⟩ := sUnion_basis_elemnts_of_open HB HU in
⟨S, subtype.val, su.trans set.sUnion_eq_Union', λ ⟨b, h⟩, sb h⟩
-/

-- this next lemma will go to mathlib one day. It's in tag00E8 currently

/-
lemma mem_subset_basis_of_mem_open {X : Type u} [T : topological_space X] {b : set (set X)}
  (hb : topological_space.is_topological_basis b) {a:X} (u : set X) (au : a ∈ u)
  (ou : _root_.is_open u) : ∃v ∈ b, a ∈ v ∧ v ⊆ u :=
(topological_space.mem_nhds_of_is_topological_basis hb).1 $ mem_nhds_sets ou au
-/