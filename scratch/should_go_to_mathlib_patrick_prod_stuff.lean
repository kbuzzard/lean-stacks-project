import algebra.group data.equiv algebra.module 

#check is_group_hom 
#print equiv.Pi_congr_right

#print out_param 

#print module 


universe u
definition Pi_lift_map₁ {γ : Type u} {F : γ → Type u} {G : γ → Type u} 
  (H : ∀ i : γ, F i → G i) : (Π i, F i) → Π i, G i := λ Fi i, H i (Fi i)
  
class foomap {α β : Type u} (f : α → β) :=
(preserves_structure : ∀ a : α, f a = f a)

instance Pi_foomap_is_foomap {γ : Type u} {F : γ → Type u} {G : γ → Type u} 
(H : ∀ i : γ, F i → G i) [∀ i, foomap (H i)] : foomap (Pi_lift_map₁ H) := sorry

example {γ : Type u} {F : γ → Type u} {G : γ → Type u} 
(H : ∀ i : γ, F i → G i) [∀ i, foomap (H i)] : foomap (Pi_lift_map₁ H) := by apply_instance

example {γ : Type u} {F : γ → Type u} {G : γ → Type u} 
(H : ∀ i : γ, F i → G i) [∀ i, foomap (H i)] : (Pi_lift_map₁ H) = (λ Fi i, H i (Fi i) : (Π i, F i) → Π i, G i) := rfl

example {γ : Type u} {F : γ → Type u} {G : γ → Type u} 
(H : ∀ i : γ, F i → G i) [∀ i, foomap (H i)] : foomap (λ Fi i, H i (Fi i) : (Π i, F i) → Π i, G i) := by apply_instance -- fails

#check module
