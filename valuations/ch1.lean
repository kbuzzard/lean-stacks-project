import algebra.group_power Kenny_comm_alg.temp set_theory.cardinal

local attribute [instance] classical.prop_decidable

universes u v

class linear_ordered_comm_group (α : Type u)
    extends comm_group α, linear_order α :=
(mul_le_mul_left : ∀ {a b : α}, a ≤ b → ∀ c : α, c * a ≤ c * b)
(mul_lt_mul_left : ∀ {a b : α}, a < b → ∀ c : α, c * a < c * b)

local infix ^ := monoid.pow

namespace linear_ordered_comm_group

variables {α : Type u} [linear_ordered_comm_group α] {x y z : α}
variables {β : Type v} [linear_ordered_comm_group β]

def is_hom (f : α → β) : Prop :=
is_group_hom f ∧ ∀ {a b : α}, a ≤ b → f a ≤ f b

structure equiv extends equiv α β :=
(is_hom : is_hom to_fun)

lemma mul_le_mul_right (H : x ≤ y) : ∀ z : α, x * z ≤ y * z :=
λ z, mul_comm z x ▸ mul_comm z y ▸ mul_le_mul_left H z

lemma one_le_mul_of_one_le_of_one_le (Hx : 1 ≤ x) (Hy : 1 ≤ y) : 1 ≤ x * y :=
have h1 : x * 1 ≤ x * y, from mul_le_mul_left Hy x,
have h2 : x ≤ x * y, by rwa mul_one x at h1,
le_trans Hx h2

lemma one_le_pow_of_one_le {n : ℕ} (H : 1 ≤ x) : 1 ≤ x^n :=
begin
  induction n with n ih,
  { exact le_refl 1 },
  { exact one_le_mul_of_one_le_of_one_le H ih }
end

lemma mul_le_one_of_le_one_of_le_one (Hx : x ≤ 1) (Hy : y ≤ 1) : x * y ≤ 1 :=
have h1 : x * y ≤ x * 1, from mul_le_mul_left Hy x,
have h2 : x * y ≤ x, by rwa mul_one x at h1,
le_trans h2 Hx

lemma pow_le_one_of_le_one {n : ℕ} (H : x ≤ 1) : x^n ≤ 1 :=
begin
  induction n with n ih,
  { exact le_refl 1 },
  { exact mul_le_one_of_le_one_of_le_one H ih }
end

lemma eq_one_of_pow_eq_one {n : ℕ} (H : x ^ nat.succ n = 1) : x = 1 :=
begin
  induction n with n ih,
  { simpa using H },
  { cases le_total x 1,
    { have h1 := mul_le_mul_right h (x ^ nat.succ n),
      dsimp [monoid.pow] at H h1,
      rw [H, one_mul] at h1,
      have h2 := pow_le_one_of_le_one h,
      exact ih (le_antisymm h2 h1) },
    { have h1 := mul_le_mul_right h (x ^ nat.succ n),
      dsimp [monoid.pow] at H h1,
      rw [H, one_mul] at h1,
      have h2 := one_le_pow_of_one_le h,
      exact ih (le_antisymm h1 h2) } }
end

lemma inv_le_one_of_one_le (H : 1 ≤ x) : x⁻¹ ≤ 1 :=
by simpa using mul_le_mul_left H (x⁻¹)

lemma inv_le_inv_of_le (H : x ≤ y) : y⁻¹ ≤ x⁻¹ :=
have h1 : _ := mul_le_mul_left H (x⁻¹ * y⁻¹),
by rwa [inv_mul_cancel_right, mul_comm x⁻¹, inv_mul_cancel_right] at h1

lemma le_one_or_inv_le_one (x : α) : x ≤ 1 ∨ x⁻¹ ≤ 1 :=
or.imp id inv_le_one_of_one_le (le_total x 1)

lemma le_or_inv_le_inv (x y : α) : x ≤ y ∨ x⁻¹ ≤ y⁻¹ :=
or.imp id inv_le_inv_of_le (le_total x y)

class is_convex (S : set α) : Prop :=
(one_mem : (1:α) ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → y ∈ S → x * y ∈ S)
(inv_mem : ∀ {x}, x ∈ S → x⁻¹ ∈ S)
(mem_of_between : ∀ {x y}, x ≤ y → y ≤ (1:α) → x ∈ S → y ∈ S)

class is_proper_convex (S : set α) extends is_convex S : Prop :=
(exists_ne : ∃ (x y : α) (hx : x ∈ S) (hy : y ∈ S), x ≠ y)

definition convex_linear_order : linear_order {S : set α // is_convex S} :=
{ le_total := λ ⟨x, hx⟩ ⟨y, hy⟩, classical.by_contradiction $ λ h,
    let ⟨h1, h2⟩ := not_or_distrib.1 h,
        ⟨m, hmx, hmny⟩ := set.not_subset.1 h1,
        ⟨n, hny, hnnx⟩ := set.not_subset.1 h2 in
    begin
      cases le_total m n with hmn hnm,
      { cases le_one_or_inv_le_one n with hn1 hni1,
        { exact hnnx (@@is_convex.mem_of_between _ hx hmn hn1 hmx) },
        { cases le_total m (n⁻¹) with hmni hnim,
          { exact hnnx (inv_inv n ▸ (@@is_convex.inv_mem _ hx $ @@is_convex.mem_of_between _ hx hmni hni1 hmx)) },
          { cases le_one_or_inv_le_one m with hm1 hmi1,
            { exact hmny (@@is_convex.mem_of_between _ hy hnim hm1 $ @@is_convex.inv_mem _ hy hny) },
            { exact hmny (inv_inv m ▸ (@@is_convex.inv_mem _ hy $ @@is_convex.mem_of_between _ hy (inv_le_inv_of_le hmn) hmi1 $ @@is_convex.inv_mem _ hy hny)) } } } },
      { cases le_one_or_inv_le_one m with hm1 hmi1,
        { exact hmny (@@is_convex.mem_of_between _ hy hnm hm1 hny) },
        { cases le_total n (m⁻¹) with hnni hmim,
          { exact hmny (inv_inv m ▸ (@@is_convex.inv_mem _ hy $ @@is_convex.mem_of_between _ hy hnni hmi1 hny)) },
          { cases le_one_or_inv_le_one n with hn1 hni1,
            { exact hnnx (@@is_convex.mem_of_between _ hx hmim hn1 $ @@is_convex.inv_mem _ hx hmx) },
            { exact hnnx (inv_inv n ▸ (@@is_convex.inv_mem _ hx $ @@is_convex.mem_of_between _ hx (inv_le_inv_of_le hnm) hni1 $ @@is_convex.inv_mem _ hx hmx)) } } } }
    end,
  .. subrel.partial_order }

def ker (f : α → β) (hf : is_hom f) : set α :=
{ x | f x = 1 }

theorem ker.is_convex (f : α → β) (hf : is_hom f) : is_convex (ker f hf) :=
{ one_mem := hf.1.one,
  mul_mem := λ x y hx hy, show f (x * y) = 1, by dsimp [ker] at hx hy; rw [hf.1 x y, hx, hy, mul_one],
  inv_mem := λ x hx, show f x⁻¹ = 1, by dsimp [ker] at hx; rw [← hf.1.inv x, hx, one_inv],
  mem_of_between := λ x y hxy hy1 hx, le_antisymm (hf.1.one ▸ hf.2 hy1) (hx ▸ hf.2 hxy) }

def height (α : Type u) [linear_ordered_comm_group α] : cardinal :=
cardinal.mk {S : set α // is_proper_convex S}

theorem height_zero_iff_subsingleton : height α = 0 ↔ subsingleton α :=
not_iff_not.1 ⟨λ h1 h2, let ⟨⟨S, hs⟩⟩ := cardinal.ne_zero_iff_nonempty.1 h1 in
    let ⟨x, y, hx, hy, hnxy⟩ := @@is_proper_convex.exists_ne _ S hs in
    hnxy $ @@subsingleton.elim h2 x y,
  λ h1, cardinal.ne_zero_iff_nonempty.2 $ sorry⟩

end linear_ordered_comm_group