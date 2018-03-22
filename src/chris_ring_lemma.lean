import algebra.group_power algebra.big_operators data.nat.choose
local infix ` ^ ` := monoid.pow
open finset nat
variable {α : Type*}

local notation f ` ∑ ` : 90 n : 90  := finset.sum (finset.range n) f

lemma sum_range_succ [add_comm_monoid α] (f : ℕ → α) (n : ℕ) : f ∑ succ n = f n + f ∑ n :=
have h : n ∉ finset.range n := by rw finset.mem_range; exact lt_irrefl _,
by rw [finset.range_succ, finset.sum_insert h]

lemma sum_range_succ' [add_comm_monoid α] (f : ℕ → α) : 
    ∀ n : ℕ, f ∑ succ n = (λ m, f (succ m)) ∑ n + f 0
| 0        := by simp
| (succ n) := by rw [sum_range_succ (λ m, f (succ m)), add_assoc, ← sum_range_succ'];
                 exact sum_range_succ _ _

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

theorem missing [comm_semiring α] (n : ℕ) (f : ℕ → α) (e : ℕ → ℕ) (r : ℕ → α)
    (s : α) : (∀ i : ℕ, i ≤ n → (f i) ^ (e i) * s = 0) →
    (sum (range (succ n)) (λ i, f i * r i)) ^ (sum (range (succ n)) e) * s = 0 :=
nat.rec_on n (λ h, by simp [mul_pow, mul_right_comm, h 0 (le_refl _)])
$ λ n hi h, begin 
  rw [sum_range_succ, add_pow, sum_mul, ← @sum_const_zero _ _ (range (succ (e ∑ succ (succ n))))],
  refine finset.sum_congr rfl (λ m hm, _),
  cases le_total m (e (succ n)) with hm' hm',
  { rw [sum_range_succ e, add_comm (e _), nat.add_sub_assoc hm', _root_.pow_add],
    simp only [mul_assoc, mul_left_comm ((λ (i : ℕ), f i * r i) ∑ succ n ^ e ∑ succ n)],
    rw hi (λ i hi, h i (le_succ_of_le hi)),
    simp },
  { rw [← nat.add_sub_cancel' hm', _root_.pow_add, mul_pow],
    simp only [mul_assoc, mul_left_comm (f (succ n) ^ e (succ n)), h],
    simp }
end

theorem missing1 [comm_semiring α] (n : ℕ) (f : ℕ → α) (e : ℕ → ℕ) (r : ℕ → α)
    (s : α) : (∀ i : ℕ, i < n → (f i) ^ (e i) * s = 0) → 
    sum (range n) (λ i, f i * r i) = 1 → s = 0 :=
nat.cases_on n (λ h₁ (h₂ : 0 = 1), mul_zero s ▸ h₂.symm ▸ (mul_one s).symm) $ λ n h₁ h₂, begin
  have := missing n f e r s (λ i hi, h₁ i (lt_succ_of_le hi)),
  rwa [sum_range_succ e, _root_.pow_add, h₂, one_pow, one_pow, one_mul, one_mul] at this,
end
