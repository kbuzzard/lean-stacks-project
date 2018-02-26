-- storing intersections of definitions in different file temporarily

import algebra.module algebra.linear_algebra.quotient_module
import tactic.ring analysis.topology.topological_space
import order.complete_lattice order.order_iso

universes u v w

@[simp] lemma quotient.lift_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift f h (quotient.mk x) = f x := rfl

@[simp] lemma quotient.lift_on_beta {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift_on (quotient.mk x) f h = f x := rfl

lemma setoid.r_of_eq {α : Sort u} [s : setoid α] {x y : α} : x = y → x ≈ y :=
eq.rec $ setoid.refl _

def nonunits (α : Type u) [comm_ring α] : set α := { x | ¬∃ y, x * y = 1 }
def nonunits' (α : Type u) [comm_ring α] : set α := { x | ¬∃ y, y * x = 1 }

theorem nonunits_left {α : Type u} [comm_ring α] {x : α} : x ∈ nonunits α → ¬∃ y, y * x = 1 :=
λ hx ⟨y, hyx⟩, hx ⟨y, mul_comm y x ▸ hyx⟩

theorem nonunits_of_left {α : Type u} [comm_ring α] {x : α} : (¬∃ y, y * x = 1) → x ∈ nonunits α :=
λ hx ⟨y, hxy⟩, hx ⟨y, mul_comm x y ▸ hxy⟩

class is_ideal {α : Type u} [comm_ring α] (S : set α) extends is_submodule S : Prop

namespace is_ideal

variables {α : Type u} [comm_ring α]
variables (S : set α) [is_ideal S] (x y : α)

lemma zero : (0:α) ∈ S := @is_submodule.zero _ _ _ _ S _

variables {S x y}

lemma add : x ∈ S → y ∈ S → x + y ∈ S :=
λ hx hy, is_submodule.add hx hy

lemma neg : x ∈ S → -x ∈ S :=
λ hx, is_submodule.neg hx

lemma of_neg : -x ∈ S → x ∈ S :=
λ hx, set.mem_of_eq_of_mem (neg_neg x).symm (is_submodule.neg hx)

lemma sub : x ∈ S → y ∈ S → x - y ∈ S :=
λ hx hy, is_submodule.sub hx hy

lemma mul_left : y ∈ S → x * y ∈ S :=
λ hy, is_submodule.smul x hy

lemma mul_right : x ∈ S → x * y ∈ S :=
λ hx, set.mem_of_eq_of_mem (mul_comm x y) (is_submodule.smul y hx)

lemma of_add_left : x + y ∈ S → x ∈ S → y ∈ S :=
λ hxy hx, set.mem_of_eq_of_mem (add_sub_cancel' x y).symm (sub hxy hx)

lemma of_add_right : x + y ∈ S → y ∈ S → x ∈ S :=
λ hxy hy, set.mem_of_eq_of_mem (add_sub_cancel x y).symm (sub hxy hy)

lemma of_sub_left : x - y ∈ S → x ∈ S → y ∈ S :=
λ hxy hx, set.mem_of_eq_of_mem (sub_sub_cancel x y).symm (sub hx hxy)

lemma of_sub_right : x - y ∈ S → y ∈ S → x ∈ S :=
λ hxy hy, set.mem_of_eq_of_mem (sub_add_cancel x y).symm (add hxy hy)

instance single_zero : is_ideal ({0}:set α) :=
{ ..is_submodule.single_zero }

instance univ : is_ideal (set.univ:set α) :=
{ ..is_submodule.univ }

end is_ideal

instance is_submodule.to_is_ideal {α : Type u} [comm_ring α] (S : set α)
  (H : is_submodule S) : is_ideal S :=
{ ..H }

class is_proper_ideal {α : Type u} [comm_ring α] (S : set α) extends is_ideal S : Prop :=
(ne_univ : S ≠ set.univ)

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

theorem is_proper_ideal.one_not_mem {α : Type u} [comm_ring α] {S : set α} [is_proper_ideal S] : (1:α) ∉ S :=
λ h, is_proper_ideal.ne_univ S $ is_submodule.univ_of_one_mem S h

theorem is_proper_ideal.not_mem_of_mul_right_one {α : Type u} [comm_ring α] {S : set α} [is_proper_ideal S]
  {u v : α} (huv : u * v = 1) : u ∉ S :=
λ hu, have h : (1:α) ∈ S, from huv ▸ is_ideal.mul_right hu,
is_proper_ideal.one_not_mem h

theorem is_proper_ideal.not_mem_of_mul_left_one {α : Type u} [comm_ring α] {S : set α} [is_proper_ideal S]
  {u v : α} (huv : u * v = 1) : v ∉ S :=
λ hv, have h : (1:α) ∈ S, from huv ▸ is_ideal.mul_left hv,
is_proper_ideal.one_not_mem h

theorem not_unit_of_mem_proper_ideal {α : Type u} [comm_ring α] (S : set α) [is_proper_ideal S] : S ⊆ nonunits' α :=
λ x hx hxy, is_proper_ideal.ne_univ S $ is_submodule.eq_univ_of_contains_unit S ⟨x, hx, hxy⟩

class is_prime_ideal {α : Type u} [comm_ring α] (S : set α) extends is_proper_ideal S : Prop :=
(mem_or_mem_of_mul_mem : ∀ {x y : α}, x * y ∈ S → x ∈ S ∨ y ∈ S)

theorem mem_or_mem_of_mul_eq_zero {α : Type u} [comm_ring α] (S : set α) [is_prime_ideal S] :
  ∀ {x y : α}, x * y = 0 → x ∈ S ∨ y ∈ S :=
λ x y hxy, have x * y ∈ S, by rw hxy; from (@is_submodule.zero α α _ _ S _ : (0:α) ∈ S),
is_prime_ideal.mem_or_mem_of_mul_mem this

local infix ^ := monoid.pow

theorem is_prime_ideal.mem_of_pow_mem {α : Type u} [comm_ring α] {S : set α} [is_prime_ideal S]
  {x : α} {n : ℕ} (hx : x^n ∈ S) : x ∈ S :=
(nat.rec_on n
   (λ h, false.elim $ is_proper_ideal.ne_univ S $
      is_submodule.univ_of_one_mem S h)
   (λ n ih h, or.cases_on
      (is_prime_ideal.mem_or_mem_of_mul_mem h)
      id ih))
hx

class is_maximal_ideal {α : Type u} [comm_ring α] (S : set α) extends is_proper_ideal S : Prop :=
(eq_or_univ_of_subset : ∀ (T : set α) [is_submodule T], S ⊆ T → T = S ∨ T = set.univ)

theorem is_maximal_ideal.mk' {α : Type u} [comm_ring α] (S : set α) [is_submodule S] :
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
λ x hx hxy, is_proper_ideal.ne_univ S $ is_submodule.eq_univ_of_contains_unit S ⟨x, hx, hxy⟩

instance is_maximal_ideal.to_is_prime_ideal {α : Type u} [comm_ring α] {S : set α} (hs : is_maximal_ideal S) : is_prime_ideal S :=
{ mem_or_mem_of_mul_mem :=
  λ x y hxy,
  have hsx : S ⊆ span (insert x S),
  from set.subset.trans (set.subset_insert x S) subset_span,
  have hsx2 : _,
  from is_maximal_ideal.eq_or_univ_of_subset _ hsx,
  have hsy : S ⊆ span (insert y S),
  from set.subset.trans (set.subset_insert y S) subset_span,
  have hsy2 : _,
  from is_maximal_ideal.eq_or_univ_of_subset _ hsy,
  begin
    rw span_insert at hsx hsx2 hsy hsy2,
    rw [set.set_eq_def, set.set_eq_def] at hsx2 hsy2,
    cases hsx2 with hx hx,
    { left,
      rw ← hx x,
      exact ⟨1, 0, @@is_submodule.zero _ _ is_submodule_span, by simp⟩ },
    { cases hsy2 with hy hy,
      { right,
        rw ← hy y,
        exact ⟨1, 0, @@is_submodule.zero _ _ is_submodule_span, by simp⟩ },
      { specialize hx 1,
        specialize hy 1,
        simp at hx hy,
        rcases hx with ⟨x1, x2, hx1, hx2⟩,
        rcases hy with ⟨y1, y2, hy1, hy2⟩,
        exfalso,
        apply is_proper_ideal.ne_univ S,
        apply is_submodule.univ_of_one_mem S,
        rw @span_eq_of_is_submodule _ _ _ _ S _ at hx1 hy1,
        exact calc
        (1:α) = (x2 + x1 * x) * (y2 + y1 * y) : by simp [hx2.symm, hy2.symm]
          ... = x2 * y2 + (y1 * y) * x2 + (x1 * x) * y2 + (x1 * y1) * (x * y) : by ring
          ... ∈ S : is_submodule.add
            (is_submodule.add
               (is_submodule.add
                  (is_submodule.smul x2 hy1)
                  (is_submodule.smul (y1 * y) hx1))
               (is_submodule.smul (x1 * x) hy1))
            (is_submodule.smul _ hxy),
        repeat { apply_instance } } }
  end }

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
  max := @@is_maximal_ideal.mk' _ (nonunits' α) hi (λ ho, ho ⟨1, mul_one 1⟩) $
    λ x T ht hst hxns hxt, have hxu : _, from classical.by_contradiction hxns,
    let ⟨y, hxy⟩ := hxu in by rw [← hxy]; exact @@is_submodule.smul _ _ ht y hxt,
  unique := λ T hmt, or.cases_on (@@is_maximal_ideal.eq_or_univ_of_subset _ hmt (nonunits' α) hi $
      λ z hz, @@not_unit_of_mem_maximal_ideal _ T hmt hz) id $
    (λ htu, false.elim $ ((set.set_eq_def _ _).1 htu 1).2 trivial ⟨1, mul_one 1⟩) }


class is_ring_hom {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : α → β) : Prop :=
(map_add : ∀ {x y}, f (x + y) = f x + f y)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)
(map_one : f 1 = 1)

namespace is_ring_hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_ring_hom f] {x y : α}

lemma map_zero : f 0 = 0 :=
calc f 0 = f (0 + 0) - f 0 : by rw [map_add f]; simp
     ... = 0 : by simp

lemma map_neg : f (-x) = -f x :=
calc f (-x) = f (-x + x) - f x : by rw [map_add f]; simp
        ... = -f x : by simp [map_zero f]

lemma map_sub : f (x - y) = f x - f y :=
by simp [map_add f, map_neg f]

end is_ring_hom

structure ring_equiv (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] extends equiv α β :=
(is_ring_hom : is_ring_hom to_fun)

namespace ring_equiv

variables {α : Type u} {β : Type v} {γ : Type w}
variables [comm_ring α] [comm_ring β] [comm_ring γ]

infix ` ≃ᵣ `:25 := ring_equiv

variable α

protected def refl : α ≃ᵣ α :=
{ is_ring_hom := by refine {..}; intros; refl,
  .. equiv.refl α }

variable {α}

protected def symm (f : α ≃ᵣ β) : β ≃ᵣ α :=
{ is_ring_hom :=
    { map_add := λ x y, calc
              f.inv_fun (x + y)
            = f.inv_fun (f.to_fun (f.inv_fun x) + f.to_fun (f.inv_fun y)) : by rw [f.right_inv, f.right_inv]
        ... = f.inv_fun (f.to_fun (f.inv_fun x + f.inv_fun y)) : by simp [f.is_ring_hom.map_add]
        ... = f.inv_fun x + f.inv_fun y : f.left_inv _,
      map_mul := λ x y, calc
              f.inv_fun (x * y)
            = f.inv_fun (f.to_fun (f.inv_fun x) * f.to_fun (f.inv_fun y)) : by rw [f.right_inv, f.right_inv]
        ... = f.inv_fun (f.to_fun (f.inv_fun x * f.inv_fun y)) : by simp [f.is_ring_hom.map_mul]
        ... = f.inv_fun x * f.inv_fun y : f.left_inv _,
      map_one := calc
              f.inv_fun 1
            = f.inv_fun (f.to_fun 1) : by simp [f.is_ring_hom.map_one]
        ... = 1 : f.left_inv 1 },
  .. equiv.symm f.to_equiv }

protected def trans (f : α ≃ᵣ β) (g : β ≃ᵣ γ) : α ≃ᵣ γ :=
{ is_ring_hom := by refine {..}; intros; unfold equiv.trans;
    simp [f.is_ring_hom.map_add, g.is_ring_hom.map_add,
      f.is_ring_hom.map_mul, g.is_ring_hom.map_mul,
      f.is_ring_hom.map_one, g.is_ring_hom.map_one],
  .. equiv.trans f.to_equiv g.to_equiv }

end ring_equiv

def is_submodule.hom_preimage {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
(f : α → β) [is_ring_hom f] (S : set β) [is_submodule S] : is_submodule (f ⁻¹' S) :=
{ zero_ := by simpa [is_ring_hom.map_zero f]; exact @is_submodule.zero β β _ _ S _,
  add_  := λ x y (hx : f x ∈ S) hy, by simp [is_ring_hom.map_add f, is_submodule.add hx hy],
  smul  := λ x y (hy : f y ∈ S), by simp [is_ring_hom.map_mul f]; exact is_submodule.smul _ hy }

def is_prime_ideal.hom_preimage {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
(f : α → β) [is_ring_hom f] (S : set β) [is_prime_ideal S] :
  @is_prime_ideal α _ ((f)⁻¹' S) :=
{ (is_submodule.hom_preimage f S : is_submodule (f ⁻¹' S)) with
  ne_univ := λ h, have (1:α) ∈ f ⁻¹' S, by rw h; trivial,
   is_proper_ideal.ne_univ S $ is_submodule.univ_of_one_mem S $ by simpa [is_ring_hom.map_one f] using this,
  mem_or_mem_of_mul_mem := λ x y, by simpa [is_ring_hom.map_mul f] using @@is_prime_ideal.mem_or_mem_of_mul_mem _ _inst_4,
  .. is_submodule.hom_preimage f S }

namespace is_ideal

variables (α : Type u) [comm_ring α] (S : set α) [is_submodule S]

instance : setoid α := is_submodule.quotient_rel S

infix ` /ᵣ `:100 := is_submodule.quotient
include S

instance quotient.has_mul : has_mul (α /ᵣ S) :=
⟨quotient.lift₂ (λ m n, ⟦m * n⟧) (λ m₁ m₂ n₁ n₂ h₁ h₂, quot.sound $
suffices (m₁ * m₂) - (n₁ * n₂) ∈ S, from this,
by rw is_submodule.quotient_rel_eq at h₁ h₂; exact calc
    (m₁ * m₂) - (n₁ * n₂) = m₁ * (m₂ - n₂) + n₂ * (m₁ - n₁) : by ring
                      ... ∈ S : is_submodule.add (is_submodule.smul m₁ h₂) (is_submodule.smul n₂ h₁))⟩

instance quotient.comm_ring (α : Type u) [comm_ring α] (S : set α) [is_submodule S] :
  comm_ring (α /ᵣ S) :=
by refine
{ mul            := (*),
  mul_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  one            := ⟦1⟧,
  one_mul        := quotient.ind _,
  mul_one        := quotient.ind _,
  left_distrib   := λ m n k, quotient.induction_on₃ m n k _,
  right_distrib  := λ m n k, quotient.induction_on₃ m n k _,
  mul_comm       := quotient.ind₂ _,
  ..is_submodule.quotient.add_comm_group S };
{ intros; apply quotient.sound; ring }

def mk' : α → α /ᵣ S := @quotient.mk _ (is_submodule.quotient_rel S)

instance god : add_comm_group (α /ᵣ S) := ring.to_add_comm_group (α /ᵣ S)
instance why : add_group (α /ᵣ S) := by apply_instance
instance plz : has_add (α /ᵣ S) := by apply_instance
instance help : comm_ring (α /ᵣ S) := by apply_instance
instance me : has_mul (α /ᵣ S) := by apply_instance

def to_quotient : is_ring_hom (mk' α S) :=
by refine {..}; intros; refl

variables (x y : α)

lemma coset_eq : ⟦x⟧ = mk' α S x := rfl
@[simp] lemma add_coset : mk' α S x + mk' α S y = mk' α S (x + y) := rfl
@[simp] lemma neg_coset : -mk' α S x = mk' α S (-x) := rfl
@[simp] lemma sub_coset : mk' α S x - mk' α S y = mk' α S (x - y) := rfl
@[simp] lemma mul_coset : mk' α S x * mk' α S y = mk' α S (x * y) := rfl
@[simp] lemma one_coset : 1 = mk' α S 1 := rfl

@[simp] lemma quotient.lift_beta {β : Sort v} (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift f h (mk' α S x) = f x := rfl

@[simp] lemma quotient.lift_on_beta {β : Sort v} (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (x : α):
quotient.lift_on (mk' α S x) f h = f x := rfl

end is_ideal

lemma is_ideal_span {α : Type u} [comm_ring α] {S : set α} :
  is_ideal (span S) :=
{ ..is_submodule_span }


class subring (α : Type u) [comm_ring α] (S : set α) : Prop :=
(add_mem : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
(neg_mem : ∀ {x}, x ∈ S → -x ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → y ∈ S → x * y ∈ S)
(one_mem : (1:α) ∈ S)

namespace subring

variables (α : Type u) [comm_ring α] (S : set α) [subring α S]

instance : comm_ring S :=
{ add            := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x + y, add_mem hx hy⟩,
  add_assoc      := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ add_assoc x y z,
  zero           := ⟨0, eq.subst (add_neg_self (1:α)) $ add_mem (one_mem S) $ neg_mem $ one_mem S⟩,
  zero_add       := λ ⟨x, hx⟩, subtype.eq $ zero_add x,
  add_zero       := λ ⟨x, hx⟩, subtype.eq $ add_zero x,
  neg            := λ ⟨x, hx⟩, ⟨-x, neg_mem hx⟩,
  add_left_neg   := λ ⟨x, hx⟩, subtype.eq $ add_left_neg x,
  add_comm       := λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.eq $ add_comm x y,
  mul            := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, mul_mem hx hy⟩,
  mul_assoc      := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ mul_assoc x y z,
  one            := ⟨1, one_mem S⟩,
  one_mul        := λ ⟨x, hx⟩, subtype.eq $ one_mul x,
  mul_one        := λ ⟨x, hx⟩, subtype.eq $ mul_one x,
  left_distrib   := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ left_distrib x y z,
  right_distrib  := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ right_distrib x y z,
  mul_comm       := λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.eq $ mul_comm x y }

@[simp] lemma add (x y : α) (hx : x ∈ S) (hy : y ∈ S) :
(⟨x, hx⟩ : S) + ⟨y, hy⟩ = ⟨x + y, add_mem hx hy⟩ := rfl

@[simp] lemma mul (x y : α) (hx : x ∈ S) (hy : y ∈ S) :
(⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ := rfl

def is_ring_hom : is_ring_hom ((λ x, x) : S → α) :=
{ map_add := λ x y, by cases x; cases y; refl,
  map_mul := λ x y, by cases x; cases y; refl,
  map_one := rfl }

end subring

namespace is_ring_hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_ring_hom f] {x y : α}

@[reducible] def ker : set α := f⁻¹' {0}
instance ker.is_submodule : is_submodule (ker f) := is_submodule.hom_preimage f {0}
instance ker.is_ideal : is_ideal (ker f) := { .. ker.is_submodule f}

@[reducible] def im : set β := { y | ∃ x, f x = y }
instance im.subring : subring β (im f) :=
{ add_mem := λ x y ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n, by simp [map_add f, hm, hn]⟩,
  neg_mem := λ x ⟨m, hm⟩, ⟨-m, by simp [map_neg f, hm]⟩,
  mul_mem := λ x y ⟨m, hm⟩ ⟨n, hn⟩, ⟨m * n, by simp [map_mul f, hm, hn]⟩,
  one_mem := ⟨(1:α), map_one f⟩ }

instance im.comm_ring : comm_ring (im f) := subring.comm_ring β (im f)

end is_ring_hom

noncomputable def first_isom (α : Type u) (β : Type v)
  [comm_ring α] [comm_ring β] (f : α → β) [is_ring_hom f] :
(α /ᵣ (is_ring_hom.ker f)) ≃ᵣ (is_ring_hom.im f) :=
{ to_fun := λ x, quotient.lift_on x (λ x, ⟨f x, x, rfl⟩ : α → is_ring_hom.im f) (λ x y hxy, subtype.eq $ calc
    f x = f (y + (x - y)) : by norm_num
    ... = f y + f (x - y) : is_ring_hom.map_add f
    ... = f y             : by simp [is_submodule.quotient_rel_eq] at hxy; simp [hxy]),
  is_ring_hom :=
    { map_add := λ x y, quotient.induction_on₂ x y (λ m n, by simp [is_ideal.coset_eq, is_ring_hom.map_add f]; refl),
      map_mul := λ x y, quotient.induction_on₂ x y (λ m n, by simp [is_ideal.coset_eq, is_ring_hom.map_mul f]; refl),
      map_one := by simp [is_ring_hom.map_one f]; refl },
  inv_fun := λ ⟨y, hy⟩, ⟦classical.some hy⟧,
  left_inv := λ x, quotient.induction_on x $
    begin
      intro y,
      have hz := @classical.some_spec _ (λ z, f z = f y) ⟨y, rfl⟩,
      simp [first_isom._match_1, is_ideal.mk', -is_ideal.coset_eq],
      simp [is_submodule.quotient_rel_eq, is_ring_hom.map_add f, hz, is_ring_hom.map_neg f]
    end,
  right_inv := λ ⟨x, hx⟩, subtype.eq (by simp [first_isom._match_1]; simpa using classical.some_spec hx) }

def topological_space.is_topological_basis' {α : Type u} [t : topological_space α] (s : set (set α)) :=
(∀ U : set α, U ∈ s → t.is_open U) ∧ 
(∀ U : set α, t.is_open U → (∀ x, x ∈ U → ∃ V : set α, V ∈ s ∧ x ∈ V ∧ V ⊆ U))

lemma topological_space.generate_from_apply {α : Type u} [t : topological_space α] (s : set (set α)) (U : set α) :
  topological_space.is_open (topological_space.generate_from s) U ↔ topological_space.generate_open s U := iff.rfl

lemma basis_is_basis' {α : Type u} [t : topological_space α] (s : set (set α)) : 
  topological_space.is_topological_basis s ↔ topological_space.is_topological_basis' s :=
begin
  split,
  { intro H,
    split,
    { intros U HU,
      rw H.2.2,
      exact topological_space.generate_open.basic U HU },
    { intros U HU x Hx,
      rw H.2.2 at HU,
      induction HU with U4 H5 U6 U7 H8 H9 H10 H11 UU12 H13 H14,
      { exact ⟨U4, H5, Hx, set.subset.refl U4⟩ },
      { have H5 : x ∈ ⋃₀ s,
        { rw H.2.1, trivial },
        rcases H5 with ⟨V, H6, H7⟩,
        exact ⟨V, H6, H7, set.subset_univ V⟩
      },
      { specialize H10 (set.inter_subset_left U6 U7 Hx),
        specialize H11 (set.inter_subset_right U6 U7 Hx),
        cases H10 with V12 H12,
        cases H11 with V13 H13,
        have H14 := H.1 V12 H12.1 V13 H13.1 x ⟨H12.2.1, H13.2.1⟩,
        rcases H14 with ⟨V, H15, H16⟩,
        refine ⟨V, H15, H16.1, _⟩,
        refine set.subset.trans H16.2 _,
        intro z,
        apply and.imp,
        { intro hz, exact H12.2.2 hz },
        { intro hz, exact H13.2.2 hz }
      },
      { rcases Hx with ⟨V, H15, H16⟩,
        rcases H14 V H15 H16 with ⟨W, H17, H18, H19⟩,
        exact ⟨W, H17, H18, λ z hz, ⟨V, H15, H19 hz⟩⟩
      }
    }
  },
  { intro H,
    split,
    { intros U1 H1 U2 H2 x H3,
      have H4 := H.1 U1 H1,
      have H5 := H.1 U2 H2,
      have H6 := H.2 (U1 ∩ U2) (topological_space.is_open_inter t U1 U2 H4 H5) x H3,
      rcases H6 with ⟨V, H7, H8, H9⟩,
      exact ⟨V, H7, H8, H9⟩
    },
    split,
    { apply set.ext,
      intro x,
      rw iff_true_right (set.mem_univ x),
      have H1 := H.2 set.univ (topological_space.is_open_univ t) x trivial,
      rcases H1 with ⟨V, H2, H3, H4⟩,
      existsi V,
      existsi H2,
      exact H3
    },
    { apply topological_space_eq,
      apply funext,
      intro U,
      apply propext,
      rw topological_space.generate_from_apply,
      split,
      { intro H1,
        have H2 := H.2 U H1,
        have H3 : U = ⋃₀ {V | ∃ x ∈ U, V ∈ s ∧ x ∈ V ∧ V ⊆ U},
        { apply set.ext,
          intro x,
          split,
          { intro H3,
            rcases H2 x H3 with ⟨V, H4⟩,
            exact ⟨V, ⟨x, H3, H4⟩, H4.2.1⟩
          },
          { intro H3,
            rcases H3 with ⟨U1, H3, H4⟩,
            rcases H3 with ⟨y, H3, H5, H6, H7⟩,
            exact H7 H4
          }
        },
        rw H3,
        apply topological_space.generate_open.sUnion,
        intros U1 H4,
        rcases H4 with ⟨U1, H4, H5, H6, H7⟩,
        apply topological_space.generate_open.basic,
        exact H5
      },
      { exact generate_from_le H.1 U }
    }
  }
end

namespace subrel

variables {α : Type u} [partial_order α] {p : α → Prop}

instance : partial_order {x // p x} :=
{ le := subrel (≤) p,
  le_refl := λ x, le_refl x,
  le_trans := λ x y z, le_trans,
  le_antisymm := λ x y hx hy, subtype.eq $ le_antisymm hx hy }

end subrel

namespace zorn

variables (α : Type u) [partial_order α] [inhabited α]

local attribute [instance] classical.prop_decidable

theorem zorn' (H : ∀ (c : set α) (x : α) (h1 : x ∈ c) (h2 : ∀ x y, x ∈ c → y ∈ c → x ≤ y ∨ y ≤ x), ∃ ub, ∀ x ∈ c, x ≤ ub) :
  ∃ M:α, ∀ x, M ≤ x → x = M :=
begin
  have : ∃ M:α, ∀ x, M ≤ x → x ≤ M,
  { apply zorn,
    { intros c hc,
      by_cases h : c = ∅,
      { simp [h] },
      { simp [set.not_eq_empty_iff_exists] at h,
        cases h with x hx,
        apply H c x hx,
        intros x y hx hy,
        by_cases hxy : x = y,
        { simp [hxy] },
        { exact hc x hx y hy hxy } } },
    intros x y z,
    exact le_trans },
  rcases this with ⟨M, hm⟩,
  existsi M,
  intros x hx,
  symmetry,
  exact le_antisymm hx (hm x hx)
end

end zorn