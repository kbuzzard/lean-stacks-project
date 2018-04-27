-- TODO
-- ask about function overloading with equiv
-- was I just an idiot and import worked fine and it was
-- in the root namespace after all?

/-
Copyright (c) 2018 Kevin Buzzard.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard

Two types are said to be *canonically isomorphic* if a mathematician
trained in the dark arts of ZFC can replace one type by another without
any fear of disruption.

This is an interesting notion, because it is "one concept" in ZFC, and
yet seems to manifest itself in several different ways
in Lean's Dependent Type Theory.
-/

import algebra.ring 

--import localization

universe zfc
--#print extfun_app

-- Here is a notion from dependent type theory.
/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
variables {α β : Type zfc}

namespace zfc

-- modded definition of equiv which only lives in one universe.
structure equiv (α : Type zfc) (β : Type zfc) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : function.left_inverse inv_fun to_fun)
(right_inv : function.right_inverse inv_fun to_fun)

--#reduce function.left_inverse inv_fun to_fun 
-- ∀ (x : α), to_fun (inv_fun x) = x
-- note round brackets -- explicitly demand the term

--#reduce function.right_inverse inv_fun to_fun
-- ∀ (x : β), to_fun (inv_fun x) = x
-- note round brackets -- explicitly demand the term

-- Here is a notion from category theory, translated into dependent type theory.
/-- The notion of being isomorphic in a category  -/
structure isom (α : Type zfc) (β : Type zfc) :=
(to_fun : α → β)
(inv_fun : β → α)
(left_inv : inv_fun ∘ to_fun = id)
(right_inv : to_fun ∘ inv_fun = id)

-- The notions of equiv and isom might be "identified" in ZFC.
-- In dependent type theory, they are same, but we can easily move between them.
-- at least if we are happy to assume quot.sound. 
-- Several people have told me that in type theory, equiv is easier to work with than isom.

-- this is congr_fun
definition equiv_of_isom : isom α β → equiv α β
| ⟨to_fun,inv_fun,left_inv,right_inv⟩ := 
⟨to_fun,inv_fun,congr_fun left_inv,congr_fun right_inv⟩

-- #print axioms equiv_of_isom -- none

-- but the other way...

--#print axioms funext -- quot.sound
--#check @funext 
--funext :
--  ∀ {α : Sort u_1} {β : α → Sort u_2} {f₁ f₂ : Π (x : α), β x},
 --   (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂

/-- this is funext -/
definition isom_of_equiv : equiv α β → isom α β
| ⟨to_fun,inv_fun,left_inv,right_inv⟩ := ⟨to_fun,inv_fun,funext left_inv,funext right_inv⟩

-- #print axioms isom_of_equiv -- quot.sound 

end zfc

open zfc
--(variable v : α → β)

-- I want my equiv to be better than theirs if one of my imports annoyingly imports data.equiv.
-- I am over-importing madly 
/-- Kenny's definition -/
structure ring_equiv (α : Type zfc) (β : Type zfc) [comm_ring α] [comm_ring β] extends equiv α β :=
(is_ring_hom : is_ring_hom to_fun)

definition fun_to_ring : (α → β) → (ring α → ring β) := λ f Hα,
{ -- this is the boring bit which needs to be automised
  one := f Hα.one,
  one_mul :=  _,--by rw [] at Hα.one_mul,

}

#exit 

#exit 

definition equiv_to_ring : equiv α β → equiv (ring α) (ring β) := λ H,
{ to_fun := λ R,_,
  inv_fun := _,
  left_inv := _,
  right_inv := _
}
#print is_ring_hom

#check @set.image -- (α → β) → set α → set β

-- instance : is_lawful_functor set :=

#exit

-- QUESTION. Using these three functions, defined in equiv I think,
-- can I write down a map between (equiv a b) and (equiv (set a) (set b))
-- and also a map between (equiv a b) and (equiv )

--still haven't gfot this straight

namespace subtype

/-- -- Restriction of a function to a function on subtypes. -/
-- set to subtype
def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀a, p a → q (f a)) :
  subtype p → subtype q
| ⟨v, hv⟩ := ⟨f v, h v hv⟩

-- should be a functor: or doesn't that make sense?


theorem map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : subtype p}
  (f : α → β) (h : ∀a, p a → q (f a)) (g : β → γ) (l : ∀a, q a → r (g a)) :
  map g l (map f h x) = map (g ∘ f) (assume a ha, l (f a) $ h a ha) x :=
by cases x with v h; refl

theorem map_id {p : α → Prop} {h : ∀a, p a → p (id a)} : map (@id α) h = id :=
funext $ assume ⟨v, h⟩, rfl

-- is that the proof that map is a functor?
end subtype

#exit 
-- evil future plan
-- structure canonically_isomorphic (α : Type zfc) (β : Type zfc) extends equiv α β :=
--(


theorem set.image (X α β : Sort*) [H : equiv α β] (f : X → α) : 
let g : X → β := H.to_fun ∘ f in
(set.image equiv.to_fun : set α → set β) $ set.range f 
#print notation ''

end equiv


-- is this there?
instance group_of_equiv [group α] (H : equiv α β) : group β := sorry

instance set_equiv_of_equiv (H : equiv α β) : equiv (set α) (set β) := sorry

-- this is =
#check @eq α β
#check @eq
-- this is == but it doesn't typecheck -/
--#check @heq α β
#print heq
