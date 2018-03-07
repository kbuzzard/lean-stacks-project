universes u v 

theorem set.subset.trans {α : Type*} {a b c : set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c :=
assume x h, bc (ab h)

def set.preimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α := {x | f x ∈ s}
infix ` ⁻¹' `:80 := set.preimage

structure presheaf_of_types (α : Type*) := 
(F : Π U : set α,  Type*)
(res : ∀ (U V : set α) (H : V ⊆ U), 
  (F U) → (F V))
(Hcomp : ∀ (U V W : set α) 
  (HUV : V ⊆ U) (HVW : W ⊆ V),
  (res U W (set.subset.trans HVW HUV)) = (res V W HVW) ∘ (res U V HUV) )

definition presheaf_of_types_pushforward
  {α : Type*}
  {β : Type*}
  (f : α → β)
  (FPT : presheaf_of_types α)
  : presheaf_of_types β :=
  { F := λ V : set β, FPT.F (set.preimage f V),
    res := λ V₁ V₂ H, 
    FPT.res (set.preimage f V₁) (set.preimage f V₂)(λ x Hx,H Hx),
    Hcomp := λ Uβ Vβ Wβ HUV HVW,rfl -- assertion violation
  }
