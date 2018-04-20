import Kenny_comm_alg.temp

universes u v

namespace localization

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables {S : set α} [is_submonoid S] (f : α → β) [is_ring_hom f]

noncomputable def extend_map_of_im_unit
  (H : ∀ s ∈ S, ∃ t, f s * t = 1) : loc α S → β :=
quotient.lift
  (λ r, f r.1 * classical.some (H r.2.1 r.2.2) : α × S → β)
  (λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩ ⟨t, hts, ht⟩,
     have h1 : f ((s1 * r2 - s2 * r1) * t) = 0,
       by simpa using ht; simp [ht, is_ring_hom.map_zero f],
     calc
          f r1 * classical.some (H s1 hs1)
        = (f r1 * 1) * classical.some (H s1 hs1) : by simp
    ... = (f r1 * (f s2 * classical.some (H s2 hs2)) * (f t * classical.some (H t hts))) * classical.some (H s1 hs1) :
            by simp [classical.some_spec (H t hts), classical.some_spec (H s2 hs2)]
    ... = (f (s2 * r1 * t) * classical.some (H t hts)) * classical.some (H s1 hs1) * classical.some (H s2 hs2) :
            by simp [is_ring_hom.map_mul f, mul_assoc, mul_comm, mul_left_comm]
    ... = (f ((s1 * r2 - s2 * r1) * t + s2 * r1 * t) * classical.some (H t hts)) * classical.some (H s1 hs1) * classical.some (H s2 hs2) :
            by simpa using ht; simp [ht]
    ... = (f (s1 * r2 * t) * classical.some (H t hts)) * classical.some (H s1 hs1) * classical.some (H s2 hs2) :
            by rw [sub_mul, sub_add_cancel]
    ... = f r2 * classical.some (H s2 hs2) * (f s1 * classical.some (H s1 hs1)) * (f t * classical.some (H t hts)) :
            by simp [is_ring_hom.map_mul f, mul_assoc, mul_comm, mul_left_comm]
    ... = f r2 * classical.some (H s2 hs2) : by simp [classical.some_spec (H s1 hs1), classical.some_spec (H t hts)])

theorem extend_map_of_im_unit.is_ring_hom (H : ∀ s ∈ S, ∃ t, f s * t = 1)
  : is_ring_hom (extend_map_of_im_unit f H) :=
{ map_add := λ x y, quotient.induction_on₂ x y $ λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩, calc
          f (s1 * r2 + s2 * r1) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))
        = f (s1 * r2 + s2 * r1) * (f s1 * classical.some (H s1 hs1)) * (f s2 * classical.some (H s2 hs2)) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2)) :
            by simp [classical.some_spec (H s1 hs1), classical.some_spec (H s2 hs2)]
    ... = (f r1 * classical.some (H s1 hs1) * (f s2 * classical.some (H s2 hs2)) + f r2 * classical.some (H s2 hs2) * (f s1 * classical.some (H s1 hs1))) * (f (s1 * s2) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))) :
            by simp [is_ring_hom.map_add f, is_ring_hom.map_mul f]; ring SOP
    ... = f r1 * classical.some (H s1 hs1) + f r2 * classical.some (H s2 hs2) :
            by simp [classical.some_spec (H s1 hs1), classical.some_spec (H s2 hs2), classical.some_spec (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))],
  map_mul := λ x y, quotient.induction_on₂ x y $ λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩, calc
          f (r1 * r2) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))
        = f (r1 * r2) * (f s1 * classical.some (H s1 hs1)) * (f s2 * classical.some (H s2 hs2)) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2)) :
            by simp [classical.some_spec (H s1 hs1), classical.some_spec (H s2 hs2)]
    ... = f r1 * classical.some (H s1 hs1) * (f r2 * classical.some (H s2 hs2)) * (f (s1 * s2) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))) :
            by simp [is_ring_hom.map_mul f, mul_assoc, mul_comm, mul_left_comm]
    ... = f r1 * classical.some (H s1 hs1) * (f r2 * classical.some (H s2 hs2)) :
            by simp [classical.some_spec (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))],
  map_one := classical.some_spec (H 1 (is_submonoid.one_mem _)) }

noncomputable def away.extend_map_of_im_unit {x : α} (H : ∃ y, f x * y = 1) : away x → β :=
extend_map_of_im_unit f $ begin
  intros s hs,
  cases hs with n hxns,
  induction n with n ih generalizing s hxns,
  { existsi (1:β),
    rw ← hxns,
    simp [is_ring_hom.map_one f] },
  { specialize ih _ rfl,
    cases H with y hy,
    cases ih with t ht,
    existsi t * y,
    rw [← hxns, pow_succ, is_ring_hom.map_mul f],
    rw [mul_assoc, ← mul_assoc _ t, ht, one_mul, hy] }
end

theorem away.extend_map_of_im_unit.is_ring_hom {x : α} (H : ∃ y, f x * y = 1) :
  is_ring_hom (away.extend_map_of_im_unit f H) :=
extend_map_of_im_unit.is_ring_hom f _


theorem unit_of_in_S (s : S) : ∃ y : loc α S, (of_comm_ring α S s) * y = 1 :=
⟨⟦(1, s)⟧, by cases s; apply quotient.sound; existsi (1:α); existsi is_submonoid.one_mem S; simp⟩

-- note that one could make the above definition constructive:

--definition inv_of_in_S (s : S) : loc α S := ⟦(1,s)⟧

--theorem inv_of_in_S_is_inv (s : S) : (of_comm_ring α S s) * inv_of_in_S s = 1 :=
--by cases s; apply quotient.sound; existsi (1:α); existsi is_submonoid.one_mem S; simp

-- note one could also make localization R[1/f] computable to an extent.

-- definition inv_of_powers (g : α) : loc α (powers g) := ⟦(1,⟨g,1,by simp⟩)⟧ 


-- some lemmas
/-
1) f invertible in R implies R[1/f] uniquely R-iso to R
2) R[1/f][1/g] uniquely R-iso to R[1/fg]
3) cor : g invertible in R[1/f] implies R[1/f] = R[1/fg] uniquely R-iso
4) cor : f invertible in R[1/g] implies R[1/g] = R[1/f][1/g] uniquely R-iso

Should have some structures: "The unique R-algebra hom between these two R-algebras"
  and note that if there's a unique R-alg hom A -> B and one B-> A then they're isos.
-/

-- extensions are R-algebra homomorphisms
theorem extend_map_extends (H : ∀ s ∈ S, ∃ t, f s * t = 1) : 
  ∀ r : α, extend_map_of_im_unit f H (of_comm_ring _ _ r) = f r :=
λ r, calc f r * classical.some (H 1 (of_comm_ring._proof_1 α S))
        = f r * (f 1 * classical.some (H 1 (of_comm_ring._proof_1 α S))) : by simp [is_ring_hom.map_one f]
    ... = f r : by simp [classical.some_spec (H 1 (of_comm_ring._proof_1 α S))]

-- R-algebra hom extensions are unique
theorem extend_map_unique (H : ∀ s ∈ S, ∃ t, f s * t = 1) (phi : loc α S → β) [is_ring_hom phi]
  (R_alg_hom : ∀ r : α, phi (of_comm_ring _ _ r) = f r) : phi = extend_map_of_im_unit f H :=
funext $ quotient.ind begin
  intro f,
  rcases f with ⟨r, s, hs⟩,
  dsimp [extend_map_of_im_unit],
  rw [← localization.mul_inv_denom, is_ring_hom.map_mul phi, R_alg_hom],
  congr,
  have h1 : of_comm_ring α S 1 = 1 := rfl,
  exact calc phi ⟦(1, ⟨s, hs⟩)⟧
           = phi ⟦(1, ⟨s, hs⟩)⟧ * (f s * classical.some (H s hs)) : by simp [classical.some_spec (H s hs)]
       ... = phi ⟦(1, ⟨s, hs⟩)⟧ * (phi (of_comm_ring _ _ s) * classical.some (H s hs)) : by rw R_alg_hom
       ... = classical.some (H s hs) : by rw [← mul_assoc, ← is_ring_hom.map_mul phi, localization.mul_denom, h1, is_ring_hom.map_one phi, one_mul]
end

-- very common use case corollaries (proofs should be trivial consequences of the above)

theorem away.extend_map_extends {x : α} (H : ∃ y, f x * y = 1) :
  ∀ r : α, away.extend_map_of_im_unit f H (of_comm_ring _ _ r) = f r :=
extend_map_extends f _

theorem away.extension_unique {x : α} (H : ∃ y, f x * y = 1) (phi : away x → β) [is_ring_hom phi]
  (R_alg_hom : ∀ r : α, phi (of_comm_ring _ _ r) = f r) : phi = away.extend_map_of_im_unit f H :=
extend_map_unique f _ phi R_alg_hom

-- map is determined by image of ring before localization

theorem unique {f g : loc α S → β} [is_ring_hom f] [is_ring_hom g] (H : ∀ x, f (of_comm_ring _ _ x) = g (of_comm_ring _ _ x)) {x : loc α S} :
  f x = g x :=
quotient.induction_on x $ λ ⟨r, s, hs⟩,
have h1 : f ⟦(1, ⟨s, hs⟩)⟧ = g ⟦(1, ⟨s, hs⟩)⟧,
from calc f ⟦(1, ⟨s, hs⟩)⟧
        = g 1 * f ⟦(1, ⟨s, hs⟩)⟧ : by simp [is_ring_hom.map_one g]
    ... = g ⟦(1, ⟨s, hs⟩)⟧ * f (of_comm_ring _ _ s) * f ⟦(1, ⟨s, hs⟩)⟧ : by rw [H, ← is_ring_hom.map_mul g, mul_denom]; refl
    ... = g ⟦(1, ⟨s, hs⟩)⟧ * f 1 : by rw [mul_assoc, ← is_ring_hom.map_mul f, mul_comm (of_comm_ring α S s), mul_denom]; refl
    ... = g ⟦(1, ⟨s, hs⟩)⟧ : by simp [is_ring_hom.map_one f],
by rw [← mul_inv_denom, is_ring_hom.map_mul f, is_ring_hom.map_mul g, H, h1]


noncomputable def localize_more_left {R : Type u} [comm_ring R] (f g) : 
  localization.loc R (powers f) → localization.loc R (powers (f * g)) :=
localization.away.extend_map_of_im_unit (localization.of_comm_ring R _) $
⟨⟦⟨g, f * g, 1, by simp⟩⟧, by simp [localization.of_comm_ring, localization.mk_eq, localization.mul_frac]⟩

noncomputable def localize_more_right {R : Type u} [comm_ring R] (f g) :
  localization.loc R (powers g) → localization.loc R (powers (f * g)) :=
localization.away.extend_map_of_im_unit (localization.of_comm_ring R _) $
⟨⟦⟨f, f * g, 1, by simp⟩⟧, by simp [localization.of_comm_ring, localization.mk_eq, localization.mul_frac, mul_comm]⟩

theorem loc_commutes (f g r : α) : 
  localize_more_left f g (localization.of_comm_ring α (powers f) r) =
  localize_more_right f g (localization.of_comm_ring α (powers g) r) :=
begin
  dsimp [localize_more_left, localize_more_right],
  rw away.extend_map_extends,
  rw away.extend_map_extends
end

-- localization to a bigger multiplicative set
noncomputable definition localize_superset {R : Type u} [comm_ring R] {S T : set R} [is_submonoid S] [is_submonoid T] (H : S ⊆ T) :
loc R S → loc R T := extend_map_of_im_unit (of_comm_ring R T) (λ s Hs, unit_of_in_S (⟨s,H Hs⟩ : T))

-- localization to a bigger multiplicative set is a ring hom
instance localize_superset.is_ring_hom {R : Type u} [comm_ring R] {S T : set R} [is_submonoid S] [is_submonoid T] (H : S ⊆ T) :
  is_ring_hom (localize_superset H) := extend_map_of_im_unit.is_ring_hom _ _ 

-- localization to a bigger multiplicative set is an R-algebra hom
theorem localize_superset.is_algebra_hom {R : Type u} [comm_ring R] {S T : set R} [is_submonoid S] [is_submonoid T] (H : S ⊆ T) :
∀ (r : R), localize_superset H (of_comm_ring _ _ r) = of_comm_ring _ _ r := extend_map_extends _ _

-- localization to a bigger multiplicative set is the unique R-algebra map from R[1/S] to R[1/T]
theorem localize_superset.unique_algebra_hom {R : Type u} [comm_ring R] {S T : set R} [is_submonoid S] [is_submonoid T] (H : S ⊆ T)
(g : loc R S → loc R T) [is_ring_hom g] (R_alg_hom : ∀ (r : R), g (of_comm_ring _ _ r) = of_comm_ring _ _ r) : 
g = localize_superset H := extend_map_unique _ _ _ R_alg_hom

end localization
