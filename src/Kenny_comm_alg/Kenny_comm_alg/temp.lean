-- storing intersections of definitions in different file temporarily

import algebra.module

universes u v

@[simp] lemma quotient.lift_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift f h (quotient.mk x) = f x := rfl

@[simp] lemma quotient.lift_on_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift_on (quotient.mk x) f h = f x := rfl

def nonunits (α : Type u) [comm_ring α] : set α := { x | ¬∃ y, x * y = 1 }
def nonunits' (α : Type u) [comm_ring α] : set α := { x | ¬∃ y, y * x = 1 }

theorem is_submodule.smul' {α : Type u} [comm_ring α] {p : set α} [c : is_submodule p]
  {x : α} (y : α) : x ∈ p → x * y ∈ p :=
λ h, calc x * y = y * x : mul_comm _ _
            ... ∈ p : is_submodule.smul y h

theorem is_submodule.eq_univ_of_contains_unit {α : Type u} [comm_ring α] (S : set α) [is_submodule S] :
(∃ x ∈ S, ∃ y, y * x = (1:α)) → S = set.univ :=
λ ⟨x, hx, y, hy⟩, set.ext $ λ z, ⟨λ hz, trivial, λ hz, calc
    z = z * (y * x) : by simp [hy]
  ... = (z * y) * x : eq.symm $ mul_assoc z y x
  ... ∈ S : is_submodule.smul (z * y) hx⟩

theorem is_submodule.univ_of_one_mem {α : Type u} [comm_ring α] (S : set α) [is_submodule S] :
(1:α) ∈ S → S = set.univ :=
λ h, set.ext $ λ z, ⟨λ hz, trivial, λ hz, by simpa using (is_submodule.smul z h : z * 1 ∈ S)⟩


class is_prime_ideal {α : Type u} [comm_ring α] (S : set α) extends is_submodule S : Prop :=
(ne_univ : S ≠ set.univ)
(mem_or_mem_of_mul_mem : ∀ {x y : α}, x * y ∈ S → x ∈ S ∨ y ∈ S)

theorem mem_or_mem_of_mul_eq_zero {α : Type u} [comm_ring α] (S : set α) [is_prime_ideal S] :
  ∀ {x y : α}, x * y = 0 → x ∈ S ∨ y ∈ S :=
λ x y hxy, have x * y ∈ S, by rw hxy; from (@is_submodule.zero α α _ _ S _ : (0:α) ∈ S),
is_prime_ideal.mem_or_mem_of_mul_mem this

class is_maximal_ideal {α : Type u} [comm_ring α] (S : set α) extends is_submodule S : Prop :=
mk' ::
  (ne_univ : S ≠ set.univ)
  (eq_or_univ_of_subset : ∀ (T : set α) [is_submodule T], S ⊆ T → T = S ∨ T = set.univ)

theorem is_maximal_ideal.mk {α : Type u} [comm_ring α] (S : set α) [is_submodule S] :
  (1:α) ∉ S → (∀ x (T : set α) [is_submodule T], S ⊆ T → x ∉ S → x ∈ T → (1:α) ∈ T) → is_maximal_ideal S :=
λ h₁ h₂,
{ _inst_2 with
  ne_univ := λ hu, have (1:α) ∈ S, by rw hu; trivial, h₁ this,
  eq_or_univ_of_subset := λ T ht hst, or.cases_on (classical.em $ ∃ x, x ∉ S ∧ x ∈ T)
    (λ ⟨x, hxns, hxt⟩, or.inr $ @@is_submodule.univ_of_one_mem _ T ht $ @@h₂ x T ht hst hxns hxt)
    (λ hnts, or.inl $ set.ext $ λ x,
       ⟨λ hxt, classical.by_contradiction $ λ hxns, hnts ⟨x, hxns, hxt⟩,
        λ hxs, hst hxs⟩) }

theorem not_unit_of_mem_maximal_ideal {α : Type u} [comm_ring α] (S : set α) [is_maximal_ideal S] : S ⊆ nonunits' α :=
λ x hx hxy, is_maximal_ideal.ne_univ S $ is_submodule.eq_univ_of_contains_unit S ⟨x, hx, hxy⟩

class local_ring (α : Type u) [comm_ring α] :=
(S : set α)
(max : is_maximal_ideal S)
(unique : ∀ T [is_maximal_ideal T], S = T)

instance local_of_nonunits_ideal {α : Type u} [comm_ring α] : (0:α) ≠ 1 →  (∀ x y ∈ nonunits' α, x + y ∈ nonunits' α) → local_ring α :=
λ hnze h, have hi : is_submodule (nonunits' α), from
{ zero_ := λ ⟨y, hy⟩, hnze $ by simpa using hy,
  add_  := h,
  smul  := λ x y hy ⟨z, hz⟩, hy ⟨x * z, by rw [← hz]; simp [mul_left_comm, mul_assoc]⟩ },
{ S := nonunits' α,
  max := @@is_maximal_ideal.mk _ (nonunits' α) hi (λ ho, ho ⟨1, mul_one 1⟩) $
    λ x T ht hst hxns hxt, have hxu : _, from classical.by_contradiction hxns,
    let ⟨y, hxy⟩ := hxu in by rw [← hxy]; exact is_submodule.smul y hxt,
  unique := λ T hmt, or.cases_on (@@is_maximal_ideal.eq_or_univ_of_subset _ hmt (nonunits' α) hi $
      λ z hz, @@not_unit_of_mem_maximal_ideal _ T hmt hz) id $
    (λ htu, false.elim $ ((set.set_eq_def _ _).1 htu 1).2 trivial ⟨1, mul_one 1⟩) }