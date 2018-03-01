-- This does not really prove tag 009Q but it will do for now.
-- It concentrates on sheaves of rings and it is currently only a
-- construction, not the proof.

import Kenny_comm_alg.Zariski
import algebra.module
import Kenny_comm_alg.temp
import tag00EJ_statement
import localization

-- stolen from Patrick Massot
-- https://github.com/PatrickMassot/lean-differential-topology/blob/f47348abf8515e23bd485683d8b351c7fd89c70f/src/indexed_product.lean

namespace indexed_product
universes u v
variable {I : Type u} -- The indexing type
variable {f : I → Type v}

instance has_mul [∀ i, has_mul $ f i] : has_mul (Π i : I, f i) := 
⟨λ x y, λ i, x i * y i⟩

instance semigroup [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
{ mul_assoc := assume a b c, by funext ; exact @semigroup.mul_assoc (f i) _ (a i) (b i) (c i),
  ..indexed_product.has_mul }

instance comm_semigroup [∀ i, comm_semigroup $ f i] : comm_semigroup (Π i : I, f i) :=
{ mul_comm := assume a b, by funext ; exact @comm_semigroup.mul_comm (f i) _ (a i) (b i),
  ..indexed_product.semigroup }

instance has_one [∀ i, has_one $ f i] : has_one (Π i : I, f i) := 
⟨λ i, 1⟩

instance has_inv [∀ i, has_inv $ f i] : has_inv (Π i : I, f i) := 
⟨λ x, λ i, (x i)⁻¹⟩

instance monoid [∀ i, monoid $ f i] : monoid (Π i : I, f i) :=
{ one_mul := assume a, by funext ; exact @monoid.one_mul (f i) _ (a i),
  mul_one := assume a, by funext ; exact @monoid.mul_one (f i) _ (a i),
  ..indexed_product.has_one,
  ..indexed_product.has_inv,
  ..indexed_product.semigroup }

instance comm_monoid [∀ i, comm_monoid $ f i] : comm_monoid (Π i : I, f i) :=
{ ..indexed_product.monoid,
  ..indexed_product.comm_semigroup }

instance group [∀ i, group $ f i] : group (Π i : I, f i) :=
{ mul_left_inv := assume a, by funext ; exact @group.mul_left_inv (f i) _ (a i),
  ..indexed_product.has_inv,
  ..indexed_product.monoid }


instance has_add [∀ i, has_add $ f i] : has_add (Π i : I, f i) := 
⟨λ x y, λ i, x i + y i⟩

instance add_semigroup [∀ i, add_semigroup $ f i] : add_semigroup (Π i : I, f i) :=
{ add_assoc := assume a b c, by funext ; exact @add_semigroup.add_assoc (f i) _ (a i) (b i) (c i),
  ..indexed_product.has_add }

instance has_zero [∀ i, has_zero $ f i] : has_zero (Π i : I, f i) := 
⟨λ i, 0⟩

instance has_neg [∀ i, has_neg $ f i] : has_neg (Π i : I, f i) := 
⟨λ x, λ i, -(x i)⟩


instance add_group [∀ i, add_group $ f i] : add_group (Π i : I, f i) :=
{ zero_add := assume a, by funext ; exact @add_group.zero_add (f i) _ (a i),
  add_zero := assume a, by funext ; exact @add_group.add_zero (f i) _ (a i),
  add_left_neg := assume a, by funext ; exact @add_group.add_left_neg (f i) _ (a i),
  ..indexed_product.has_zero,
  ..indexed_product.has_neg,
  ..indexed_product.add_semigroup }


instance add_comm_group [∀ i, add_comm_group $ f i] : add_comm_group (Π i : I, f i) :=
{ add_comm := assume a b, by funext ; exact @add_comm_group.add_comm (f i) _ (a i) (b i),
  ..indexed_product.add_group }

instance distrib [∀ i, distrib $ f i] : distrib (Π i : I, f i) :=
{ left_distrib := assume a b c, by funext ; exact @distrib.left_distrib (f i) _ (a i) (b i) (c i),
  right_distrib := assume a b c, by funext ; exact @distrib.right_distrib (f i) _ (a i) (b i) (c i),
  ..indexed_product.has_add,
  ..indexed_product.has_mul }

instance ring [∀ i, ring $ f i] : ring (Π i : I, f i) :=
{ ..indexed_product.distrib,
  ..indexed_product.monoid,
  ..indexed_product.add_comm_group }

-- this is what we want
instance comm_ring [∀ i, comm_ring $ f i] : comm_ring (Π i : I, f i) :=
{ ..indexed_product.comm_semigroup,
..indexed_product.ring }

end indexed_product
-- now back to stuff not stolen from Patrick

universes u v
#check Zariski.is_open
--    U = -Spec.V E → topological_space.is_open (Zariski α) U

theorem D_f_are_a_basis {R : Type u} [comm_ring R] : ∀ U : set (X R), topological_space.is_open (Zariski R) U → ∃ α : Type v, ∃ f : α → R, U = set.Union (Spec.D' ∘ f) := sorry

definition structure_sheaf_on_union {R : Type u} [comm_ring R] {α : Type} (f : α → R) := 
  {x : (Π i : α, localization.loc R (powers $ f i)) // ∀ j k : α, localise_more_left (f j) (f k) (x j) = localise_more_right (f j) (f k) (x k) } 

-- a theorem says that this is a subring.

definition structure_sheaf (R : Type u) [comm_ring R] : {U : set (X R) // topological_space.is_open (Zariski R) U} → Type u :=
λ ⟨U,HU⟩, let exf := D_f_are_a_basis U HU in let fH := classical.some_spec exf in structure_sheaf_on_union (classical.some fH)

-- the pair consisting of Spec(R) and its structure sheaf are an affine scheme, although it is currently not even clear
-- from the definition that everything is well-defined (I choose a cover; I still didn't do the work to check that
-- the resulting ring is independent of choices (or even that it is a ring!)

-- Just begun to think about general schemes below.
/-
structure scheme :=
(α : Type u)
(T :topological_space α)
(O_X : {U : set α // T.is_open U} → Type v)
(O_X_sheaf_of_rings : sheaf_of_rings O_X) -- TODO
(locally_affine : ∃ β : Type v, ∃ cov : β → {U : set α // T.is_open U}, 
  set.Union (λ b, (cov b).val) = set.univ ∧
  ∀ b : β, ∃ R : Type w, comm_ring R ∧ true)

-/
