import localization

universe u

--local infix ^ := monoid.pow

namespace localization_away

variables (R : Type u) [comm_ring R] (f : R)

def r : R × ℕ → R × ℕ → Prop :=
λ x y, ∃ t : ℕ, (f ^ x.2 * y.1 - f ^ y.2 * x.1) * f ^ t = 0

local infix ≈ := r R f

theorem refl : ∀ (x : R × ℕ), x ≈ x :=
λ ⟨r₁, s₁⟩, ⟨0, by simp⟩

theorem symm : ∀ (x y : R × ℕ), x ≈ y → y ≈ x :=
λ ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨t, ht⟩, ⟨t, calc
        (f ^ s₂ * r₁ - f ^ s₁ * r₂) * f ^ t
      = -((f ^ s₁ * r₂ - f ^ s₂ * r₁) * f ^ t) : by simp [add_mul]
  ... = 0 : by rw ht; simp⟩

theorem trans : ∀ (x y z : R × ℕ), x ≈ y → y ≈ z → x ≈ z :=
λ ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨t, ht⟩ ⟨t', ht'⟩,
⟨s₂ + t' + t, calc
         (f ^ s₁ * r₃ - f ^ s₃ * r₁) * f ^ (s₂ + t' + t)
       = f ^ t' * f ^ s₃ * ((f ^ s₁ * r₂ - f ^ s₂ * r₁) * f ^ t) + f ^ t * f ^ s₁ * ((f ^ s₂ * r₃ - f ^ s₃ * r₂) * f ^ t') :
           by simp [pow_add, mul_left_comm, mul_add, mul_comm]
   ... = 0 : by rw [ht, ht']; simp⟩

instance : setoid (R × ℕ) :=
⟨r R f, refl R f, symm R f, trans R f⟩

def loc := quotient $ localization_away.setoid R f

@[reducible] def mk : R → ℕ → loc R f :=
λ a r, @quotient.mk _ (localization_away.setoid R f) (a, r)

private def add_aux : R × ℕ → R × ℕ → loc R f :=
λ ⟨r₁, s₁⟩ ⟨r₂, s₂⟩, mk R f (f ^ s₁ * r₂ + f ^ s₂ * r₁) (s₁ + s₂)

instance : has_add (loc R f) :=
⟨@quotient.lift₂ _ _ _
 (localization_away.setoid R f) (localization_away.setoid R f)
 (add_aux R f) $
 λ ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨r₄, s₄⟩ ⟨t₅, ht₅⟩ ⟨t₆, ht₆⟩,
 @quotient.sound _ (localization_away.setoid R f) _ _
   ⟨t₆ + t₅, by dsimp; from calc
         (f ^ (s₁ + s₂) * (f ^ s₃ * r₄ + f ^ s₄ * r₃) - f ^ (s₃ + s₄) * (f ^ s₁ * r₂ + f ^ s₂ * r₁)) * (f ^ (t₆ + t₅))
       = f ^ s₁ * f ^ s₃ * ((f ^ s₂ * r₄ - f ^ s₄ * r₂) * f ^ t₆) * f ^ t₅ + f ^ s₂ * f ^ s₄ * ((f ^ s₁ * r₃ - f ^ s₃ * r₁) * f ^ t₅) * f ^ t₆ : by rw [pow_add, pow_add, pow_add]; ring
   ... = 0 : by rw [ht₆, ht₅]; simp⟩⟩

private def neg_aux : R × ℕ → loc R f :=
λ ⟨r, s⟩, mk R f (-r) s

instance : has_neg (loc R f) :=
⟨@quotient.lift _ _ (localization_away.setoid R f) (neg_aux R f) $
 λ ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨t, ht⟩,
 @quotient.sound _ (localization_away.setoid R f) _ _
 ⟨t, by dsimp; from calc
         (f ^ s₁ * -r₂ - f ^ s₂ * -r₁) * f ^ t
       = -((f ^ s₁ * r₂ - f ^ s₂ * r₁) * f ^ t) : by ring
   ... = 0 : by rw ht; simp⟩⟩

private def mul_aux : R × ℕ → R × ℕ → loc R f :=
λ x y, mk R f (x.1 * y.1) (x.2 + y.2)

instance : has_mul (loc R f) :=
⟨@quotient.lift₂ _ _ _
 (localization_away.setoid R f) (localization_away.setoid R f)
 (mul_aux R f) $
 λ ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨r₄, s₄⟩ ⟨t₅, ht₅⟩ ⟨t₆, ht₆⟩,
 @quotient.sound _ (localization_away.setoid R f) _ _
 ⟨t₆ + t₅, by dsimp; from calc
         (f ^ (s₁ + s₂) * (r₃ * r₄) - f ^ (s₃ + s₄) * (r₁ * r₂)) * f ^ (t₆ + t₅)
       = f ^ t₆ * ((f ^ s₁ * r₃ - f ^ s₃ * r₁) * f ^ t₅) * r₂ * f ^ s₄ + f ^ t₅ * ((f ^ s₂ * r₄ - f ^ s₄ * r₂) * f ^ t₆) * r₃ * f ^ s₁ :
           by rw [pow_add, pow_add, pow_add]; simp [mul_left_comm, mul_add, mul_comm,mul_assoc]
   ... = 0 : by rw [ht₅, ht₆]; simp⟩⟩

instance : comm_ring (loc R f) :=
by letI := localization_away.setoid R f; refine
{ add            := has_add.add,
  add_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  zero           := ⟦⟨0, 0⟩⟧,
  zero_add       := quotient.ind _,
  add_zero       := quotient.ind _,
  neg            := has_neg.neg,
  add_left_neg   := quotient.ind _,
  add_comm       := quotient.ind₂ _,
  mul            := has_mul.mul,
  mul_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  one            := ⟦⟨1, 0⟩⟧,
  one_mul        := quotient.ind _,
  mul_one        := quotient.ind _,
  left_distrib   := λ m n k, quotient.induction_on₃ m n k _,
  right_distrib  := λ m n k, quotient.induction_on₃ m n k _,
  mul_comm       := quotient.ind₂ _ };
{ intros,
  try {cases a with r₁ s₁},
  try {cases b with r₂ s₂},
  try {cases c with r₃ s₃},
  apply quotient.sound,
  existsi 0,
  simp [pow_add, mul_left_comm, mul_add, mul_comm] }

def of_comm_ring : R → loc R f :=
λ r, mk R f r 0

instance : is_ring_hom (of_comm_ring R f) :=
{ map_add := λ x y, by apply quotient.sound; simp,
  map_mul := λ x y, by apply quotient.sound; simp,
  map_one := rfl }

def to_localization : loc R f → localization.away f :=
@quotient.lift _ _ (localization_away.setoid R f)
  (λ x, ⟦(⟨x.1, f ^ x.2, x.2, rfl⟩ : R × powers f)⟧)
  (λ x y ⟨t, ht⟩, by apply quotient.sound; existsi f^t;
    existsi (⟨t, rfl⟩ : f ^ t ∈ powers f); exact ht)

variables {R} (g : R)

def more_left : loc R f → loc R (f * g) :=
@quotient.lift _ _ (localization_away.setoid R f)
  (λ x, mk R (f * g) (g ^ x.2 * x.1) x.2)
  (λ x y ⟨t, ht⟩, by apply quotient.sound; existsi t; clear _x _fun_match;
     cases x with r₁ s₁; cases y with r₂ s₂; from calc
          ((f * g) ^ s₁ * (g ^ s₂ * r₂) + -((f * g) ^ s₂ * (g ^ s₁ * r₁))) * (f * g) ^ t
        = g ^ s₁ * g ^ s₂ * ((f ^ s₁ * r₂ - f ^ s₂ * r₁) * f ^ t) * g ^ t : by simp [mul_pow]; ring
    ... = 0 : by rw ht; simp )

def more_right : loc R g → loc R (f * g) :=
@quotient.lift _ _ (localization_away.setoid R g)
  (λ x, mk R (f * g) (f ^ x.2 * x.1) x.2)
  (λ x y ⟨t, ht⟩, by apply quotient.sound; existsi t; clear _x _fun_match;
     cases x with r₁ s₁; cases y with r₂ s₂; from calc
          ((f * g) ^ s₁ * (f ^ s₂ * r₂) + -((f * g) ^ s₂ * (f ^ s₁ * r₁))) * (f * g) ^ t
        = f ^ s₁ * f ^ s₂ * ((g ^ s₁ * r₂ - g ^ s₂ * r₁) * g ^ t) * f ^ t : by simp [mul_pow]; ring
    ... = 0 : by rw ht; simp )

end localization_away