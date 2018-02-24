import Kenny_comm_alg.temp

universe u

namespace is_ideal

variables {α : Type u} [comm_ring α] (S S₁ S₂ S₃ S₄ T T₁ T₂ : set α)
variables [is_ideal S] [is_ideal S₁] [is_ideal S₂] [is_ideal S₃] [is_ideal S₄]

@[reducible] def add_ideal : set α :=
{ x | ∃ y z, y ∈ T₁ ∧ z ∈ T₂ ∧ x = y + z }

infix + := add_ideal

variables {S₁ S₂}

instance add.is_ideal : is_ideal (S₁ + S₂) :=
{ zero_ := ⟨0, 0, zero S₁, zero S₂, by simp⟩,
  add_  := λ x₁ x₂ ⟨y₁, z₁, hy₁, hz₁, hx₁⟩ ⟨y₂, z₂, hy₂, hz₂, hx₂⟩,
    ⟨y₁ + y₂, z₁ + z₂, add hy₁ hy₂, add hz₁ hz₂, by simp [hx₁, hx₂]⟩,
  smul  := λ x₁ x₂ ⟨y, z, hy, hz, hx⟩,
    ⟨x₁ * y, x₁ * z, mul_left hy, mul_left hz, by simp [hx, mul_add]⟩ }

theorem subset_add_left : S₁ ⊆ S₁ + S₂ :=
λ x hx, ⟨x, 0, hx, zero S₂, eq.symm $ add_zero x⟩

theorem subset_add_right : S₂ ⊆ S₁ + S₂ :=
λ x hx, ⟨0, x, zero S₁, hx, eq.symm $ zero_add x⟩

theorem add_self : S₁ + S₁ = S₁ :=
set.ext $ λ x,
⟨λ ⟨y, z, hy, hz, hx⟩, set.mem_of_eq_of_mem hx $ add hy hz,
 λ hx, subset_add_left hx⟩

@[reducible] def mul_ideal : set α :=
span { x | ∃ y z, y ∈ T₁ ∧ z ∈ T₂ ∧ x = y * z}

infix * := mul_ideal

instance mul.is_ideal : is_ideal (S₁ * S₂) :=
{ ..is_submodule_span }

instance inter.is_ideal : is_ideal (S₁ ∩ S₂) :=
{ zero_ := ⟨zero S₁, zero S₂⟩,
  add_  := λ x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩, ⟨add hx1 hy1, add hx2 hy2⟩,
  smul  := λ x y ⟨hy1, hy2⟩, ⟨mul_left hy1, mul_left hy2⟩ }

instance sInter.is_ideal (S : set $ set α) (h : ∀ A ∈ S, is_ideal A) : is_ideal (⋂₀ S) :=
{ zero_ := λ A ha, @@zero _ A (h A ha),
  add_  := λ x y hx hy A ha, @@add _ (h A ha) (hx A ha) (hy A ha),
  smul  := λ x y hy A ha, @@mul_left _ (h A ha) (hy A ha) }

instance sInter'.is_ideal (SS : set $ {S : set α // is_ideal S}) :
  is_ideal {x | ∀ S:{S : set α // is_ideal S}, S ∈ SS → x ∈ S.val} :=
{ zero_ := λ A ha, @@zero _ A.1 A.2,
  add_  := λ x y hx hy A ha, @@add _ A.2 (hx A ha) (hy A ha),
  smul  := λ x y hy A ha, @@mul_left _ A.2 (hy A ha) }

variables {S₁ S₂ S₃ S₄}

theorem mem_add {x y : α} : x ∈ S₁ → y ∈ S₂ → x + y ∈ S₁ + S₂ :=
λ hx hy, ⟨x, y, hx, hy, rfl⟩

theorem mem_mul {x y : α} : x ∈ S₁ → y ∈ S₂ → x * y ∈ S₁ * S₂ :=
λ hx hy, subset_span ⟨x, y, hx, hy, rfl⟩

theorem add_comm : S₁ + S₂ = S₂ + S₁ :=
set.ext $ λ x,
⟨λ ⟨y, z, hy, hz, hx⟩, ⟨z, y, hz, hy, add_comm y z ▸ hx⟩,
 λ ⟨y, z, hy, hz, hx⟩, ⟨z, y, hz, hy, add_comm y z ▸ hx⟩⟩

lemma span_ext {T₁ T₂ : set α} : (∀ x, x ∈ T₁ ↔ x ∈ T₂) → span T₁ = span T₂ :=
λ hx, congr_arg span $ set.ext hx

theorem mul_comm : S₁ * S₂ = S₂ * S₁ :=
span_ext $ λ x,
⟨λ ⟨y, z, hy, hz, hx⟩, ⟨z, y, hz, hy, mul_comm y z ▸ hx⟩,
 λ ⟨y, z, hy, hz, hx⟩, ⟨z, y, hz, hy, mul_comm y z ▸ hx⟩⟩

theorem add_assoc : (S₁ + S₂) + S₃ = S₁ + (S₂ + S₃) :=
set.ext $ λ x,
⟨λ ⟨pq, r, ⟨p, q, hp, hq, hpq⟩, hr, hx⟩, ⟨p, q + r, hp, ⟨q, r, hq, hr, rfl⟩, add_assoc p q r ▸ hpq ▸ hx⟩,
 λ ⟨p, qr, hp, ⟨q, r, hq, hr, hqr⟩, hx⟩, ⟨p + q, r, ⟨p, q, hp, hq, rfl⟩, hr, (add_assoc p q r).symm ▸ hqr ▸ hx⟩⟩

theorem mul_subset_left : S₁ * S₂ ⊆ S₁ :=
span_minimal _inst_3.to_is_submodule $
λ z ⟨p, q, hp, hq, hz⟩, calc
    z = p * q : hz
  ... ∈ S₁    : mul_right hp

theorem mul_subset_right : S₁ * S₂ ⊆ S₂ :=
span_minimal _inst_4.to_is_submodule $
λ z ⟨p, q, hp, hq, hz⟩, calc
    z = p * q : hz
  ... ∈ S₂    : mul_left hq

theorem mul_subset_inter : S₁ * S₂ ⊆ S₁ ∩ S₂ :=
λ x hx, ⟨mul_subset_left hx, mul_subset_right hx⟩

theorem add_univ : S₁ + set.univ = set.univ :=
set.ext $ λ x, ⟨λ hx, trivial, λ hx, subset_add_right hx⟩

theorem univ_add : set.univ + S₁ = set.univ :=
set.ext $ λ x, ⟨λ hx, trivial, λ hx, subset_add_left hx⟩

theorem add_zero : S₁ + ({0}:set α) = S₁ :=
set.ext $ λ x,
⟨λ ⟨y, z, hy, hz, hx⟩, by simp at hz; simp [hz] at hx; simpa [hx],
 λ hx, subset_add_left hx⟩

theorem zero_add : ({0}:set α) + S₁ = S₁ :=
set.ext $ λ x,
⟨λ ⟨y, z, hy, hz, hx⟩, by simp at hy; simp [hy] at hx; simpa [hx],
 λ hx, subset_add_right hx⟩

lemma subset_span_of_subset {T₁ T₂ : set α} : T₁ ⊆ T₂ → T₁ ⊆ span T₂ :=
λ h, set.subset.trans h subset_span

theorem mul_univ : S₁ * set.univ = S₁ :=
span_eq _inst_3.to_is_submodule
  (λ x ⟨y, z, hy, hz, hx⟩, by rw hx; exact mul_right hy)
  (subset_span_of_subset $
   λ x hx, ⟨x, 1, hx, trivial, eq.symm $ mul_one x⟩)

theorem univ_mul : set.univ * S₁ = S₁ :=
span_eq _inst_3.to_is_submodule
  (λ x ⟨y, z, hy, hz, hx⟩, by rw hx; exact mul_left hz)
  (subset_span_of_subset $
   λ x hx, ⟨1, x, trivial, hx, eq.symm $ one_mul x⟩)

theorem mul_zero : S₁ * ({0}:set α) = ({0}:set α) :=
span_eq is_submodule.single_zero
  (λ x ⟨y, z, hy, hz, hx⟩, by simp at hz; simp [hx, hz])
  (subset_span_of_subset $
   λ x hx, ⟨0, 0, by simp at hx; simp [hx, zero]⟩)

theorem zero_mul : ({0}:set α) * S₁ = ({0}:set α) :=
span_eq is_submodule.single_zero
  (λ x ⟨y, z, hy, hz, hx⟩, by simp at hy; simp [hx, hy])
  (subset_span_of_subset $
   λ x hx, ⟨0, 0, by simp at hx; simp [hx, zero]⟩)

end is_ideal