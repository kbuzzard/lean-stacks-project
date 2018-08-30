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
{ zero_ := ⟨0, 0, is_ideal.zero S₁, is_ideal.zero S₂, by simp⟩,
  add_  := λ x₁ x₂ ⟨y₁, z₁, hy₁, hz₁, hx₁⟩ ⟨y₂, z₂, hy₂, hz₂, hx₂⟩,
    ⟨y₁ + y₂, z₁ + z₂, is_ideal.add hy₁ hy₂, is_ideal.add hz₁ hz₂, by simp [hx₁, hx₂]⟩,
  smul  := λ x₁ x₂ ⟨y, z, hy, hz, hx⟩,
    ⟨x₁ * y, x₁ * z, mul_left hy, mul_left hz, by simp [hx, mul_add]⟩ }

theorem subset_add_left : S₁ ⊆ S₁ + S₂ :=
λ x hx, ⟨x, 0, hx, is_ideal.zero S₂, eq.symm $ add_zero x⟩

theorem subset_add_right : S₂ ⊆ S₁ + S₂ :=
λ x hx, ⟨0, x, is_ideal.zero S₁, hx, eq.symm $ zero_add x⟩

theorem add_self : S₁ + S₁ = S₁ :=
set.ext $ λ x,
⟨λ ⟨y, z, hy, hz, hx⟩, set.mem_of_eq_of_mem hx $ is_ideal.add hy hz,
 λ hx, subset_add_left hx⟩

@[reducible] def mul_ideal : set α :=
span { x | ∃ y z, y ∈ T₁ ∧ z ∈ T₂ ∧ x = y * z}

infix * := mul_ideal

instance mul.is_ideal : is_ideal (S₁ * S₂) :=
{ ..is_submodule_span }

instance inter.is_ideal : is_ideal (S₁ ∩ S₂) :=
{ zero_ := ⟨is_ideal.zero S₁, is_ideal.zero S₂⟩,
  add_  := λ x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩, ⟨is_ideal.add hx1 hy1, is_ideal.add hx2 hy2⟩,
  smul  := λ x y ⟨hy1, hy2⟩, ⟨mul_left hy1, mul_left hy2⟩ }

instance sInter.is_ideal (S : set $ set α) (h : ∀ A ∈ S, is_ideal A) : is_ideal (⋂₀ S) :=
{ zero_ := λ A ha, @@is_ideal.zero _ A (h A ha),
  add_  := λ x y hx hy A ha, @@is_ideal.add _ (h A ha) (hx A ha) (hy A ha),
  smul  := λ x y hy A ha, @@mul_left _ (h A ha) (hy A ha) }

instance sInter'.is_ideal (SS : set $ {S : set α // is_ideal S}) :
  is_ideal {x | ∀ S:{S : set α // is_ideal S}, S ∈ SS → x ∈ S.val} :=
{ zero_ := λ A ha, @@is_ideal.zero _ A.1 A.2,
  add_  := λ x y hx hy A ha, @@is_ideal.add _ A.2 (hx A ha) (hy A ha),
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
set.ext $ λ x, ⟨λ hx, show true,by trivial, λ hx, subset_add_right hx⟩

theorem univ_add : set.univ + S₁ = set.univ :=
set.ext $ λ x, ⟨λ hx, show true, by trivial, λ hx, subset_add_left hx⟩

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
   λ x hx, ⟨x, 1, hx, show true, by trivial, eq.symm $ mul_one x⟩)

theorem univ_mul : set.univ * S₁ = S₁ :=
span_eq _inst_3.to_is_submodule
  (λ x ⟨y, z, hy, hz, hx⟩, by rw hx; exact mul_left hz)
  (subset_span_of_subset $
   λ x hx, ⟨1, x, show true, by trivial, hx, eq.symm $ one_mul x⟩)

theorem mul_zero : S₁ * ({0}:set α) = ({0}:set α) :=
span_eq is_submodule.single_zero
  (λ x ⟨y, z, hy, hz, hx⟩, by simp at hz; simp [hx, hz])
  (subset_span_of_subset $
   λ x hx, ⟨0, 0, by simp at hx; simp [hx, is_ideal.zero]⟩)

theorem zero_mul : ({0}:set α) * S₁ = ({0}:set α) :=
span_eq is_submodule.single_zero
  (λ x ⟨y, z, hy, hz, hx⟩, by simp at hy; simp [hx, hy])
  (subset_span_of_subset $
   λ x hx, ⟨0, 0, by simp at hx; simp [hx, is_ideal.zero]⟩)

/-
(0,2) -> (x+y, 0)
(1,0) -> (0, 1) [(x+y)^(1+0-1) = (0)*x^1+(1)*y^0]
(1,1) -> (1, 1) [(x+y)^(1+1-1) = (1)*x^1+(1)*y^1]
(1,2) -> (x+2y, 1) [(x+y)^(1+2-1) = (x+2y)*x^1+(1)*y^2]
(1,3) -> (x^2+3xy+3y^2, 1) [(x+y)^3 = (x^2+3xy+3y^2)*x^1+(1)*y^3]
(2,2) -> (x+3y, y+3x)
(3,2) -> (x+4y, y^2+4xy+6x^2)
(4,1) -> (1, y^3+4xy^2+6x^2y+4x^3)
(4,2) -> (x+5y, y^3+5xy^2+10x^2y+10x^3)
(4,3) -> (x^2+6xy+15y^2, y^3+6xy^2+14x^2y+20x^3)
(4,4) -> (x^3+7x^2y+21xy^2+35y^3, y^3+7xy^2+21x^2y+35x^3)

(x,y,1,0) : 0
(x,y,1,1) : 1 = 0*(x+y) + 1*y^0
(x,y,1,2) : x+2y = 1*(x+y) + 1*y^1
(x,y,1,3) : x^2+3xy+3y^2 = (x+2y)*(x+y) + 1*y^2

(y,x,2,3): y^2+4xy+6x^2 = (y+3x)(y+x) + 3x^2
(y,x,2,4): y^3+5xy^2+10x^2y+10x^3 = (y^2+4xy+6x^2)(y+x) + 4x^3

A(x,y,4,3) = A(x,y,4,2)*(x+y)+(5C2)y^3
A(x,y,4,4) = A(x,y,4,3)*(x+y)+(6C3)y^3

(x+y)^(4+3-1) = x^4(x^2+6xy+15y^2) + y^3(y^3+6xy^2+15x^2y+20x^3)
(x+y)^(5+3-1)
= (x^4(x^2+6xy+15y^2) + y^3(y^3+6xy^2+15x^2y+20x^3))(x+y)
= x^5(x^2+6xy+15y^2) + x^4(x^2+6xy+15y^2)y + y^3(y^3+6xy^2+15x^2y+20x^3)(x+y)
= x^5(x^2+6xy+15y^2) + x^4(x^2+6xy+15y^2)y + y^3(y^3+6xy^2+15x^2y+20x^3)(x+y)

(x+y)^(1+2+1) = (x^2+4xy+6y^2)*x^2 + (y+4x)*y^3
(x+y)^(1+1+1) = (x+3y)*x^2 + (y+3x)*y^2
(x+y)^(1+0+1) = (1)*x^2 + (y+2x)*y^1
(x+y)^(0+0+1) = (1)*x^1 + (1)*y^1

A(x,y,0,0) = 1
A(x,y,0,1) = x+2y = (1)*(x+y)+y
A(x,y,0,2) = x^2+3xy+3y^2
A(x,y,0,3) = x^3+4x^2y+6xy^2+4y^3 = A(x,y,0,2)*(x+y)+y^3
A(x,y,1,0) = 1
A(x,y,1,1) = x+3y = (1)*(x+y)+2y
A(x,y,1,2) = x^2+4xy+6y^2 = (x+3y)*(x+y)+3y^2 [remark: 3C1]
A(x,y,1,3) = x^3+5x^2y+10xy^2+10y^3
A(x,y,2,0) = 1
A(x,y,2,1) = x+4y
A(x,y,2,2) = x^2+5xy+10y^2
A(x,y,2,3) = x^3+6x^2y+15xy^2+20y^3 = A(x,y,1,3) + y*A(x,y,2,2)

-/

def some_binomial_boi (x y : α) : nat → nat → α
| m     0     := 1
| 0     (n+1) := (some_binomial_boi 0 n) * (x + y) + y^(n+1)
| (m+1) (n+1) := some_binomial_boi m (n+1) + y * some_binomial_boi (m+1) n

lemma some_lemma_boi (x y : α) (n : nat) : some_binomial_boi x y n 0 = 1 :=
by cases n; refl

theorem some_binomial_theorem_boi (x y : α) (m n : nat) :
  (x + y)^(m+n+1) = (some_binomial_boi x y m n)*x^(m+1) + (some_binomial_boi y x n m)*y^(n+1) :=
begin
  induction m with m m_ih generalizing n;
  induction n with n n_ih,
  { simp [some_binomial_boi] },
  { rw nat.zero_add at n_ih ⊢,
    unfold pow at n_ih ⊢,
    unfold monoid.pow at n_ih ⊢,
    rw n_ih,
    unfold some_binomial_boi,
    rw some_lemma_boi,
    unfold pow,
    unfold monoid.pow,
    ring },
  { specialize m_ih 0,
    simp [pow_succ] at m_ih ⊢,
    rw m_ih,
    unfold some_binomial_boi,
    rw some_lemma_boi,
    unfold pow,
    unfold monoid.pow,
    ring },
  { calc  (x + y) ^ (nat.succ m + nat.succ n + 1)
        = x * (x + y) ^ (m + (n + 1) + 1) + y * (x + y) ^ (nat.succ m + n + 1) :
            by rw [pow_succ, add_mul]; simp [nat.succ_eq_add_one]
    ... = x * (some_binomial_boi x y m (n + 1) * x ^ (m + 1) + some_binomial_boi y x (n + 1) m * y ^ ((n + 1) + 1)) +
          y * (some_binomial_boi x y (nat.succ m) n * x ^ (nat.succ m + 1) + some_binomial_boi y x n (nat.succ m) * y ^ (n + 1)) :
            by rw [m_ih, n_ih]
    ... = some_binomial_boi x y (nat.succ m) (nat.succ n) * x ^ (nat.succ m + 1) +
          some_binomial_boi y x (nat.succ n) (nat.succ m) * y ^ (nat.succ n + 1) :
            by unfold some_binomial_boi; unfold pow; unfold monoid.pow; simp [nat.succ_eq_add_one]; ring SOP; ac_refl }
end

def radical : set α := {x | ∃ n : ℕ, x ^ (n+1) ∈ S}

instance radical.is_ideal : is_ideal (radical S) :=
{ zero_ := ⟨0, by simp [is_ideal.zero]⟩,
  add_  := λ x y ⟨m, hxms⟩ ⟨n, hyns⟩,
    ⟨m + n, by rw some_binomial_theorem_boi;
     exact is_ideal.add
       (is_ideal.mul_left hxms)
       (is_ideal.mul_left hyns)⟩,
  smul  := λ x y ⟨n, hyns⟩,
    ⟨n, by dsimp [(•)]; rw mul_pow;
       exact is_ideal.mul_left hyns⟩ }

theorem subset_radical : S ⊆ radical S :=
λ x hx, ⟨0, by simpa⟩

end is_ideal