import algebra.group_power algebra.big_operators data.nat.choose
-- This appears to be a proof of the binomial theorem by Chris.
open finset nat
variable {α : Type*}

local notation f ` ∑ ` : 90 n : 90  := finset.sum (finset.range n) f

theorem add_pow [comm_semiring α] (x y : α) : ∀ n : ℕ,
    (x + y)^n = (λ m, x^m * y^(n - m) * choose n m) ∑ succ n
| 0        := by simp
| (succ n) :=
have h₁ : x * (x^n * y^(n - n) * choose n n) = x^succ n * y^(succ n - succ n)
    * choose (succ n) (succ n) :=
  by simp [_root_.pow_succ, mul_assoc, mul_comm, mul_left_comm],
have  h₂ : y * (x^0 * y^(n - 0) * choose n 0) = x^0 * y^(succ n - 0) * choose (succ n) 0 := 
  by simp [_root_.pow_succ, mul_assoc, mul_comm, mul_left_comm],
have h₃ : (λ m, x * (x^m * y^(n - m) * choose n m) + y * (x^succ m * y^(n - succ m)
    * choose n (succ m))) ∑ n 
    = (λ m, x^succ m * y^(succ n - succ m) * ↑(choose (succ n) (succ m))) ∑ n := 
  finset.sum_congr rfl $ λ m hm, begin 
      rw finset.mem_range at hm,
      rw [← mul_assoc y, ← mul_assoc y, mul_right_comm y, ← _root_.pow_succ, add_one, ← succ_sub hm],
      simp [succ_sub_succ, _root_.pow_succ, choose_succ_succ, mul_add, mul_comm, 
          mul_assoc, mul_left_comm]
    end,
by rw [_root_.pow_succ, add_pow, add_mul, finset.mul_sum, finset.mul_sum, sum_range_succ, sum_range_succ',
    sum_range_succ, sum_range_succ', add_assoc, ← add_assoc (_ ∑ n), ← finset.sum_add_distrib, h₁, h₂, h₃]


