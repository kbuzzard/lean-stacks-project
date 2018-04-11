import ring_theory.localization

universes u v

namespace localization

variables (α : Type u) [comm_ring α] (S : set α) [is_submonoid S]

theorem mul_denom (r s : α) (hs : s ∈ S) : @@has_mul.mul (localization.has_mul α S) (⟦⟨r, s, hs⟩⟧ : loc α S) (of_comm_ring α S s) = of_comm_ring α S r :=
quotient.sound $ ⟨1, is_submonoid.one_mem S, by simp [mul_comm]⟩

theorem mul_inv_denom (r s : α) (hs : s ∈ S) : @@has_mul.mul (localization.has_mul α S) (of_comm_ring α S r) (⟦⟨1, s, hs⟩⟧ : loc α S) = (⟦⟨r, s, hs⟩⟧ : loc α S) :=
quotient.sound $ ⟨1, is_submonoid.one_mem S, by simp⟩

section simp_lemmas

variables (f f₁ f₂ : α × S)

def mk : loc α S := ⟦f₁⟧
lemma mk_eq : ⟦f₁⟧ = mk α S f₁ := rfl
@[simp] lemma add_frac : mk α S f₁ + mk α S f₂ =
  mk α S ⟨f₁.2.1 * f₂.1 + f₂.2.1 * f₁.1, f₁.2.1 * f₂.2.1,
    is_submonoid.mul_mem f₁.2.2 f₂.2.2⟩ :=
by cases f₁; cases f₂; cases f₁_snd; cases f₂_snd; refl
@[simp] lemma neg_frac : -mk α S f =
  mk α S ⟨-f.1, f.2⟩ :=
by cases f; cases f_snd; refl
@[simp] lemma sub_frac : mk α S f₁ - mk α S f₂ =
  mk α S ⟨f₂.2.1 * f₁.1 - f₁.2.1 * f₂.1, f₁.2.1 * f₂.2.1,
    is_submonoid.mul_mem f₁.2.2 f₂.2.2⟩ :=
by simp; refl
@[simp] lemma mul_frac : mk α S f₁ * mk α S f₂ =
  mk α S ⟨f₁.1 * f₂.1, f₁.2.1 * f₂.2.1,
    is_submonoid.mul_mem f₁.2.2 f₂.2.2⟩ :=
by cases f₁; cases f₂; cases f₁_snd; cases f₂_snd; refl
lemma one_frac : 1 = mk α S ⟨1, 1, is_submonoid.one_mem S⟩ := rfl
lemma zero_frac : 0 = mk α S ⟨0, 1, is_submonoid.one_mem S⟩ := rfl

@[simp] lemma quotient.lift_beta {β : Sort v} (f : α × S → β) (h : ∀ a b, a ≈ b → f a = f b) (x : α × S) :
quotient.lift f h (mk α S x) = f x := rfl

@[simp] lemma quotient.lift_on_beta {β : Sort v} (f : α × S → β) (h : ∀ a b, a ≈ b → f a = f b) (x : α × S) :
quotient.lift_on (mk α S x) f h = f x := rfl

@[simp] lemma div_self {y : α} {H : y ∈ S} : mk α S (y, ⟨y, H⟩) = 1 :=
quotient.sound ⟨1, is_submonoid.one_mem S, by simp⟩

end simp_lemmas

end localization

-- Factoids (not to go to mathlib):

instance : add_comm_group int := ring.to_add_comm_group int
instance : add_group int := by apply_instance

def frac_int_to_rat : localization.quotient_ring ℤ → ℚ :=
λ f, quotient.lift_on f (λ ⟨r, s, hs⟩, rat.mk r s) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
have hsnz₁ : s₁ ≠ 0,
from localization.ne_zero_of_mem_non_zero_divisors hs₁,
have hsnz₂ : s₂ ≠ 0,
from localization.ne_zero_of_mem_non_zero_divisors hs₂,
have htnz : t ≠ 0,
from localization.ne_zero_of_mem_non_zero_divisors hts,
begin
  cases eq_zero_or_eq_zero_of_mul_eq_zero ht with hrs htz,
  { change rat.mk r₁ s₁ = rat.mk r₂ s₂,
    rw sub_eq_zero at hrs,
    rw rat.mk_eq hsnz₁ hsnz₂,
    simp only [mul_comm, hrs] },
  {  exfalso,
     exact htnz htz }
end

lemma coe_denom_ne_zero (r : ℚ) : (↑r.denom:ℤ) ≠ 0 :=
λ hn, ne_of_gt r.pos $ int.of_nat_inj hn

def frac_int_of_rat : ℚ → localization.quotient_ring ℤ :=
λ r, ⟦⟨r.num, r.denom, λ z hz,
or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero hz) id
  (λ hz, false.elim $ coe_denom_ne_zero r hz)⟩⟧

theorem frac_int_to_rat_to_frac_int : ∀ f, frac_int_of_rat (frac_int_to_rat f) = f :=
λ f, quotient.induction_on f $ λ ⟨r, s, hs⟩, quotient.sound
⟨1, is_submonoid.one_mem _,
   suffices r * ↑(rat.mk r s).denom = (rat.mk r s).num * s,
   from show (↑(rat.mk r s).denom * r - s * (rat.mk r s).num) * 1 = 0,
     by simp [mul_comm, this],
   have hnd : (↑(rat.mk r s).denom:ℤ) ≠ 0,
     from coe_denom_ne_zero $ rat.mk r s,
   have hns : s ≠ 0,
     from localization.ne_zero_of_mem_non_zero_divisors hs,
   have _, from rat.num_denom $ rat.mk r s,
   by rwa ← rat.mk_eq hns hnd ⟩

theorem rat_to_frac_int_to_rat : ∀ r, frac_int_to_rat (frac_int_of_rat r) = r :=
λ ⟨n, d, h, c⟩, eq.symm $ rat.num_denom _

def canonical : equiv (localization.quotient_ring ℤ) (ℚ) :=
⟨frac_int_to_rat, frac_int_of_rat,
   frac_int_to_rat_to_frac_int,
   rat_to_frac_int_to_rat⟩

def dyadic_rat := localization.away (2:ℤ)
