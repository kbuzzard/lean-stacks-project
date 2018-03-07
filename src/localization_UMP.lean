import localization

universes u v

namespace localization

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables {S : set α} [is_submonoid α S] (f : α → β) [is_ring_hom f]

noncomputable def extend_map_of_im_unit
  (H : ∀ s ∈ S, ∃ t, f s * t = 1) : loc α S → β :=
quotient.lift
  (λ ⟨r, s, hs⟩, f r * classical.some (H s hs) : α × S → β)
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
  map_one := classical.some_spec (H 1 _) }

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
    rw [← hxns, monoid.pow, is_ring_hom.map_mul f],
    rw [mul_assoc, ← mul_assoc _ t, ht, one_mul, hy] }
end

theorem away.extend_map_of_im_unit.is_ring_hom {x : α} (H : ∃ y, f x * y = 1) :
  is_ring_hom (away.extend_map_of_im_unit f H) :=
extend_map_of_im_unit.is_ring_hom f _

theorem unit_of_in_S (s : S) : ∃ y : loc α S, (of_comm_ring α S s) * y = 1 :=
⟨⟦(1, s)⟧, by cases s; apply quotient.sound; existsi (1:α); existsi is_submonoid.one_mem S; simp⟩
set_option pp.proofs true
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


end localization
