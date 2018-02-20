import analysis.topology.topological_space
noncomputable theory

local attribute [instance] classical.prop_decidable

universe u

section is_prime_ideal

class is_ideal (α : Type u) [comm_ring α] (S : set α) : Prop :=
(zero_mem : (0 : α) ∈ S)
(add_mem : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → x * y ∈ S)

class is_prime_ideal {α : Type u} [comm_ring α] (S : set α) extends is_ideal α S : Prop :=
(ne_univ : S ≠ set.univ)
(mem_or_mem_of_mul_mem : ∀ {x y : α}, x * y ∈ S → x ∈ S ∨ y ∈ S)

theorem is_prime_ideal.one_not_mem {α : Type u} [comm_ring α] (S : set α) [is_prime_ideal S] :
  (1:α) ∉ S :=
λ h, is_prime_ideal.ne_univ S $ set.ext $ λ z,
⟨λ hz, trivial,
 λ hz, calc z = 1 * z : by simp
          ... ∈ S : is_ideal.mul_mem h⟩

end is_prime_ideal

def topological_space.of_closed {α : Type u} (T : set (set α))
  (H1 : ∅ ∈ T)
  (H2 : ∀ A ⊆ T, ⋂₀ A ∈ T)
  (H3 : ∀ A B ∈ T, A ∪ B ∈ T) :
  topological_space α :=
{ is_open := λ X, -X ∈ T,
  is_open_univ := by simp [H1],
  is_open_inter := λ s t hs ht, by simpa [set.compl_inter] using H3 (-s) (-t) hs ht,
  is_open_sUnion := λ s hs, by rw set.compl_sUnion; exact H2 (set.compl '' s) (λ z ⟨y, hy, hz⟩, by simpa [hz.symm] using hs y hy) }

section generate

variables {α : Type u} [comm_ring α] (S : set α)

def generate : set α :=
{ x | ∀ (T : set α) [is_ideal α T], S ⊆ T → x ∈ T }

instance generate.is_ideal : is_ideal α (generate S) :=
{ zero_mem := λ T ht hst, @@is_ideal.zero_mem _ T ht,
  add_mem  := λ x y hx hy T ht hst, @@is_ideal.add_mem _ ht (@hx T ht hst) (@hy T ht hst),
  mul_mem  := λ x y hx T ht hst, @@is_ideal.mul_mem _ ht (@hx T ht hst) }

theorem subset_generate : S ⊆ generate S :=
λ x hx T ht hst, hst hx

end generate

class t0_space (α : Type u) [topological_space α] :=
(t0 : ∀ x y, x ≠ y → ∃ U:set α, is_open U ∧ (xor (x ∈ U) (y ∈ U)))



section Zariski

parameters (α : Type u) [comm_ring α]

def X := {P : set α // is_prime_ideal P}

def V : set α → set X :=
λ E, {P | E ⊆ P.val}

theorem V_set_eq_V_generate (S : set α) : V S = V (generate S) :=
set.ext $ λ P,
⟨λ hp z hz, @hz P.val P.property.to_is_ideal hp,
 λ hp z hz, hp $ subset_generate S hz⟩

def Zariski : topological_space X :=
topological_space.of_closed {A | ∃ E, V E = A}
  ⟨{(1:α)}, set.ext $ λ ⟨P, hp⟩,
     ⟨λ h, @@is_prime_ideal.one_not_mem _ P hp $ by simpa [V] using h,
      λ h, false.elim h⟩⟩
(λ T ht, ⟨⋃₀ {E | ∃ A ∈ T, V E = A}, set.ext $ λ ⟨P, hp⟩,
   ⟨λ hpv A hat,
      begin
        cases ht hat with E he,
        rw ← he,
        intros z hz,
        apply hpv,
        existsi E,
        existsi (⟨A, hat, he⟩ : ∃ A ∈ T, V E = A),
        exact hz
      end,
    λ hz x ⟨E, ⟨A, H, hvea⟩, hxe⟩,
      begin
        have h1 := hz A H,
        rw ← hvea at h1,
        exact h1 hxe,
      end⟩⟩)
(λ A B ⟨Ea, ha⟩ ⟨Eb, hb⟩,
   ⟨generate Ea ∩ generate Eb,
    set.ext $ λ ⟨P, hp⟩,
    ⟨λ hz, or_iff_not_and_not.2 $ λ ⟨hpa, hpb⟩,
       begin
         rw ← ha at hpa,
         rw ← hb at hpb,
         cases not_forall.1 hpa with wa hwa,
         cases not_forall.1 hpb with wb hwb,
         cases not_imp.1 hwa with hwa1 hwa2,
         cases not_imp.1 hwb with hwb1 hwb2,
         have : wa * wb ∈ generate Ea ∩ generate Eb,
         { split,
           { apply is_ideal.mul_mem (subset_generate Ea hwa1) },
           { rw mul_comm,
             apply is_ideal.mul_mem (subset_generate Eb hwb1) } },
         cases is_prime_ideal.mem_or_mem_of_mul_mem (hz this) with hwap hwbp,
         exact hwa (λ h, hwap),
         exact hwb (λ h, hwbp),
       end,
     λ hz y ⟨hy1, hy2⟩, or.cases_on hz
       (λ hpa, begin
          rw ← ha at hpa,
          rw V_set_eq_V_generate at hpa,
          exact hpa hy1
        end)
       (λ hpb, begin
          rw ← hb at hpb,
          rw V_set_eq_V_generate at hpb,
          exact hpb hy2
        end)⟩⟩)

instance Zariski.t0 : @t0_space X Zariski :=
begin
  constructor,
  intros x y hxy,
  cases x with x hx,
  cases y with y hy,
  have h1 : ¬ x = y,
  { intro h,
    apply hxy,
    exact subtype.eq h },
  rw set.set_eq_def at h1,
  rw not_forall at h1,
  cases h1 with z hz,
  existsi -(V {z}),
  split,
  { existsi {z},
    rw set.compl_compl },
  rw iff_def at hz,
  rw not_and_distrib at hz,
  cases hz;
  rw not_imp at hz,
  { cases hz with hzx hzy,
    right,
    split,
    { intro h,
      apply hzy,
      apply h,
      exact set.mem_singleton z },
    { intro h,
      apply h,
      intros m hm,
      rw set.mem_singleton_iff at hm,
      rw hm,
      exact hzx } },
  { cases hz with hzy hzx,
    left,
    split,
    { intro h,
      apply hzx,
      apply h,
      exact set.mem_singleton z },
    { intro h,
      apply h,
      intros m hm,
      rw set.mem_singleton_iff at hm,
      rw hm,
      exact hzy } }
end

end Zariski
