definition foo : ℕ → ℕ := sorry 

structure bar :=
(baz : ℕ → ℕ)
(H : baz = foo)

#print axioms bar.mk
