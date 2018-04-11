theorem W : 0 = 1 → false := dec_trivial 

theorem X : 1000 * 1000 + 0 = 1000 * 1000 + 1 → false := λ H, W (nat.add_left_cancel H)

example : 1000 * 1000 + 0 = 1000 * 1000 + 1 := rfl -- no problem

#eval 2+2
