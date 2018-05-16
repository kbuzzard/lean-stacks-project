import data.list.basic 
open list 
lemma foldr_ext {α : Type*} {β : Type*} {l : list α} (f f' : α → β → β) (s : β)
  (H : ∀ a ∈ l, ∀ b : β, f a b = f' a b) : foldr f s l = foldr f' s l :=
begin induction l with h l IH, {simp}, -- base case}
  simp *,
  suffices : foldr f s l = foldr f' s l,
    rw this,
  apply IH,
  intros a Ha,
  apply H,
  -- simp still no work
  simp * {contextual := tt} -- this work

end

lemma got_it (P Q R S : Prop) (IH : (P → R) → S) (H0 : P → Q) (H' : Q → R) : S := 
begin
--simp *, -- fails
simp * {contextual := tt},
end 
