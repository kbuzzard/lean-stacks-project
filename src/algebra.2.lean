import algebra.module

universes u v w u₁ v₁

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

section bilinear

variables {α : Type u} [comm_ring α]
include α

variables {β : Type v} {γ : Type w} {α₁ : Type u₁} {β₁ : Type v₁}
variables [module α β] [module α γ] [module α α₁] [module α β₁]

structure is_bilinear_map {β γ α₁}
  [module α β] [module α γ] [module α α₁]
  (f : β → γ → α₁) : Prop :=
(add_pair : ∀ x y z, f (x + y) z = f x z + f y z)
(pair_add : ∀ x y z, f x (y + z) = f x y + f x z)
(smul_pair : ∀ r x y, f (r • x) y = r • f x y)
(pair_smul : ∀ r x y, f x (r • y) = r • f x y)

variables {f : β → γ → α₁} (hf : is_bilinear_map f)
include hf

theorem is_bilinear_map.zero_pair : ∀ y, f 0 y = 0 :=
λ y, calc f 0 y
        = f (0 + 0) y - f 0 y : by rw [hf.add_pair 0 0 y]; simp
    ... = 0 : by simp

theorem is_bilinear_map.pair_zero : ∀ x, f x 0 = 0 :=
λ x, calc f x 0
        = f x (0 + 0) - f x 0 : by rw [hf.pair_add x 0 0]; simp
    ... = 0 : by simp

theorem is_bilinear_map.linear_pair (y : γ) : is_linear_map (λ x, f x y) :=
{ add  := λ m n, hf.add_pair m n y,
  smul := λ r m, hf.smul_pair r m y }

theorem is_bilinear_map.pair_linear (x : β) : is_linear_map (λ y, f x y) :=
{ add  := λ m n, hf.pair_add x m n,
  smul := λ r m, hf.pair_smul r x m }

theorem is_bilinear_map.smul_smul : ∀ r₁ r₂ x y, f (r₁ • x) (r₂ • y) = (r₁ * r₂) • f x y :=
λ r₁ r₂ x y, by rw [hf.smul_pair, hf.pair_smul, mul_smul]


variables {g : α₁ → β₁} (hg : is_linear_map g)
include hg

theorem is_bilinear_map.comp : is_bilinear_map (λ x y, g (f x y)) :=
{ add_pair  := λ x y z, by rw [hf.add_pair, hg.add],
  pair_add  := λ x y z, by rw [hf.pair_add, hg.add],
  smul_pair := λ r x y, by rw [hf.smul_pair, hg.smul],
  pair_smul := λ r x y, by rw [hf.pair_smul, hg.smul] }

end bilinear



class algebra (α : out_param $ Type u) [comm_ring α] (β : Type v) extends module α β, has_mul β :=
(mul_bilinear : is_bilinear_map $ @has_mul.mul β _)

class alternative_algebra (α : out_param $ Type u) [comm_ring α] (β : Type v) extends algebra α β :=
(mul_self_zero : ∀ x : β, x * x = 0)

class associative_algebra (α : out_param $ Type u) [comm_ring α] (β : Type v) extends algebra α β :=
(mul_assoc : ∀ x y z : β, (x * y) * z = x * (y * z))

class power_associative_algebra (α : out_param $ Type u) [comm_ring α] (β : Type v) extends algebra α β :=
(pow_assoc : ∀ x : β, (x * x) * x = x * (x * x))

class commutative_algebra (α : out_param $ Type u) [comm_ring α] (β : Type v) extends algebra α β :=
(mul_comm : ∀ x y : β, x * y = y * x)

class unitary_algebra (α : out_param $ Type u) [comm_ring α] (β : Type v) extends algebra α β, has_one β :=
(mul_one : ∀ x : β, x * 1 = x)
(one_mul : ∀ x : β, 1 * x = x)

class unitary_division_algebra (α : out_param $ Type u) [comm_ring α] (β : Type v) extends unitary_algebra α β :=
(zero_ne_one : (0:β) ≠ (1:β))
(left_inv : ∀ x y : β, ∃ z, z * x = y)
(right_inv : ∀ x y : β, ∃ z, x * z = y)

class star_algebra (α : out_param $ Type u) [comm_ring α] (β : Type v) extends unitary_division_algebra α β, has_inv β :=
(inv_inv : ∀ x : β, (x⁻¹)⁻¹ = x)
(mul_inv : ∀ x y : β, (x * y)⁻¹ = y⁻¹ * x⁻¹)

class lie_algebra (α : out_param $ Type u) [comm_ring α] (β : Type v) extends alternative_algebra α β :=
(jacobi : ∀ x y z : β, x * (y * z) + y * (z * x) + z * (x * y) = 0)



class unitary_associative_commutative_algebra (α : out_param $ Type u) [comm_ring α] (β : Type v) extends unitary_algebra α β :=
(mul_assoc : ∀ x y z : β, (x * y) * z = x * (y * z))
(mul_comm : ∀ x y : β, x * y = y * x)

instance unitary_associative_commutative_algebra.has_mul (α : out_param $ Type u) [comm_ring α] (β : Type v) [unitary_associative_commutative_algebra α β] : has_mul β :=
by apply_instance

def unitary_associative_commutative_algebra.of_is_ring_hom
  {α : Type u} [comm_ring α] {β : Type v} [comm_ring β]
  (f : α → β) [is_ring_hom f] : unitary_associative_commutative_algebra α β :=
{ smul := λ x y, f x * y,
  smul_add := λ r x y, by simp [mul_add],
  add_smul := λ r₁ r₂ x, by simp [is_ring_hom.map_add f, add_mul],
  mul_smul := λ r₁ r₂ x, by simp [is_ring_hom.map_mul f, mul_assoc],
  one_smul := λ x, by simp [is_ring_hom.map_one f],
  mul_bilinear :=
    { add_pair  := add_mul,
      pair_add  := mul_add,
      smul_pair := λ r x y, mul_assoc (f r) x y,
      pair_smul := λ r x y, mul_left_comm x (f r) y },
  .. _inst_2 }

namespace unitary_associative_commutative_algebra

variables {α : Type u} [comm_ring α]
variables {β : Type v} [unitary_associative_commutative_algebra α β]
include α

def to_comm_ring : comm_ring β :=
{ left_distrib  := (algebra.mul_bilinear β).pair_add,
  right_distrib := (algebra.mul_bilinear β).add_pair,
  ..module.to_add_comm_group β, .._inst_2 }

local attribute [instance] to_comm_ring

def to_is_ring_hom : is_ring_hom (λ x:α, (x • 1:β)) :=
{ map_add := λ x y, add_smul,
  map_mul := λ x y, (congr_arg _ (unitary_algebra.mul_one 1).symm).trans ((algebra.mul_bilinear β).smul_smul x y 1 1).symm,
  map_one := one_smul }

end unitary_associative_commutative_algebra



section lie_algebra

variables {α : Type u} [comm_ring α]
variables {β : Type v} [lie_algebra α β] (x y : β)

include α β

def lie_algebra.has_mul : has_mul β := by apply_instance

local attribute [instance] lie_algebra.has_mul

theorem lie_algebra.anti_commutative  : x * y = -(y * x) :=
have h1 : _ := alternative_algebra.mul_self_zero (x + y),
sorry

theorem lie_algebra.flexible  : (x * y) * x = x * (y * x) :=
have h1 : _ := @lie_algebra.jacobi α _inst_1 β _inst_2 x x y,
have h2 : _ := @lie_algebra.jacobi α _inst_1 β _inst_2 x y y,
begin end

end lie_algebra
