universe u 
variables (X : Type u) (P : set (set X))

definition stalk1 (x : X) :=
Σ U : {U : set X // x ∈ U ∧ P U}, ℕ

definition stalk2 (x : X) (U : set X) (Hx : x ∈ U) :=
Σ (PU : P U), ℕ

structure stalk3 (x : X) :=
(U : set X) (Hx : x ∈ U) (PU : P U) (n : ℕ)

#check stalk3 

definition r (X) (P) (x)  : stalk3 X P x → stalk3 X P x → Prop := sorry 


#print and 
