import algebra.big_operators data.real.cau_seq tactic.ring algebra.archimedean data.nat.choose analysis.limits

open nat is_absolute_value

variables {α : Type*} {β : Type*} (f g : ℕ → α) (n m : ℕ)

local infix `^` := monoid.pow
local notation f ` ∑ ` : 90 n : 90  := finset.sum (finset.range n) f

section sum_range
variable [add_comm_monoid α]

lemma sum_range_succ : f ∑ succ n = f n + f ∑ n :=
have h : n ∉ finset.range n := by rw finset.mem_range; exact lt_irrefl _,
by rw [finset.range_succ, finset.sum_insert h]

lemma sum_range_succ' : ∀ n : ℕ, f ∑ succ n = (λ m, f (succ m)) ∑ n + f 0
| 0        := by simp
| (succ n) := by rw [sum_range_succ (λ m, f (succ m)), add_assoc, ← sum_range_succ'];
                 exact sum_range_succ _ _


lemma sum_range_comm : f ∑ n = (λ m, f (n - (succ m))) ∑ n :=
begin
  induction n with n hi,
  { simp },
  { rw [sum_range_succ, sum_range_succ', hi, succ_sub_one, add_comm],
    simp [succ_sub_succ] }
end

end sum_range

theorem binomial [comm_semiring α] (x y : α) : ∀ n : ℕ,
    (x + y)^n = (λ m, x^m * y^(n - m) * choose n m) ∑ succ n
| 0        := by simp
| (succ n) :=
begin
  rw [_root_.pow_succ, binomial, add_mul, finset.mul_sum, finset.mul_sum, sum_range_succ, sum_range_succ',
      sum_range_succ, sum_range_succ', add_assoc, ← add_assoc (_ ∑ n), ← finset.sum_add_distrib],
  have h₁ : x * (x^n * y^(n - n) * choose n n) = x^succ n * y^(succ n - succ n)
      * choose (succ n) (succ n) :=
    by simp [_root_.pow_succ, mul_assoc, mul_comm, mul_left_comm],
  have  h₂ : y * (x^0 * y^(n - 0) * choose n 0) = x^0 * y^(succ n - 0) * choose (succ n) 0 := 
    by simp [_root_.pow_succ, mul_assoc, mul_comm, mul_left_comm],
  have h₃ : (λ m, x * (x^m * y^(n - m) * choose n m) + y * (x^succ m * y^(n - succ m)
      * choose n (succ m))) ∑ n 
      = (λ m, x^succ m * y^(succ n - succ m) * ↑(choose (succ n) (succ m))) ∑ n := 
    finset.sum_congr rfl 
      begin 
        assume m hm,
        rw finset.mem_range at hm,
        rw [← mul_assoc y, ← mul_assoc y, mul_right_comm y, ← _root_.pow_succ, add_one, ← succ_sub hm],
        simp [succ_sub_succ, _root_.pow_succ, choose_succ_succ, mul_add, mul_comm, 
            mul_assoc, mul_left_comm]
      end,
  rw [h₁, h₂, h₃]
end

#check binomial