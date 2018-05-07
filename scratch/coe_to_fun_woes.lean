import data.equiv 
/- this file contains the lines

instance : has_coe_to_fun (α ≃ β) :=
⟨_, to_fun⟩

-/

-- this fails:
--theorem XXX {α β : Type} : has_coe_to_fun (equiv α β) := by apply_instance



variables {α β : Type} (e : equiv α β) (a : α)

#check (⇑e : α → β)
#print has_coe_to_fun
#print notation ⇑ 
#print coe_fn 
#check e   
-- #check (a : e)