--import data.list.basic algebra.big_operators data.fintype
import data.finsupp Kenny_comm_alg.Zariski

local infix ` ^ ` := monoid.pow 

local attribute [instance] classical.prop_decidable

theorem exists_of_not_forall_not {α : Type*} (P : α → Prop) : (¬ (∀ a : α, ¬ P a)) → (∃ a : α, P a) := 
not_forall_not.1 

section generate
universes u 

open finsupp 

variables {α : Type u} [comm_ring α] (S : set α)

-- generate S = { x | ∀ (T : set α) [is_submodule T], S ⊆ T → x ∈ T }

def generate' : set α :=
{ x | ∃ f : S →₀ α, x = f.sum (λ s a, a*s) }

#print notation →₀ -- it means finsupp
#print finsupp
#check map_domain_comp
#check finset.sum_mul
#print notation •
#print finsupp.sum


instance generate'.is_ideal : is_submodule (generate' S) :=
{ zero_ := ⟨0,eq.symm finsupp.sum_zero_index⟩,
  add_  := λ b c ⟨f,Hf⟩ ⟨g,Hg⟩, ⟨f+g,eq.symm (begin rw Hf,rw Hg,apply sum_add_index;simp [add_mul],end)⟩,
  smul  := λ c b ⟨f,Hf⟩,⟨⟨λ s, c * (f s),@set.finite_subset _ _ f.property _ 
    (λ x (H1 : ¬ (c * f.val x = 0)) H2,H1 (by rw H2;simp))
  ⟩,begin
  rw Hf,
  unfold has_scalar.smul,
  rw mul_comm c _,
  conv begin
  to_lhs,
  show finset.sum (support f) (λ (s : ↥S) (a : α), a * ↑s) * c,
  end,
--  show finset.sum (support f) (λ (s : ↥S) (a : α), a * ↑s) * c =
--    sum ⟨λ (s : ↥S), c * ⇑f s, _⟩ (λ (s : ↥S) (a : α), a * ↑s),
  --exact @finset.sum_mul _ _ _ _ _ _ _,
  end⟩
}
  --λ x y hy T ht hst, @@is_submodule.smul _ _ ht _ (@hy T ht hst) }


theorem generate_eq_generate' : generate S = generate' S :=
begin
apply set.eq_of_subset_of_subset,
{ intros x Hx,
  apply exists_of_not_forall_not,
  intro H1,
  revert Hx,


}
end





/-
namespace hidden
open hidden 

inductive two
| zero : two
| one : two

#print two 


instance two_has_zero : has_zero hidden.two := ⟨hidden.two.zero⟩

theorem is_locally_zero_implies_is_zero {R : Type*} [comm_ring R] (r : R)


example (R : Type) [comm_ring R] (n : ℕ) (a : fin n → R) (e : fin n → ℕ)
(r : R) (H : ∀ i : fin n, (a i) ^ (e i) * r = 0) :
(sum (univ) a) ^ (sum (univ) e) * r = 0 := sorry

-/
