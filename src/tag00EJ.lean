import Kenny_comm_alg.Zariski localization_UMP
import Kenny_comm_alg.ideal_operations
import massot_indexed_products
import data.fintype
import data.set.finite
import group_theory.submonoid
import tactic.ring
import chris_ring_lemma
local attribute [instance] classical.prop_decidable

universe u

open finset classical quotient 
universes v w

theorem finset.sum_bind1 {α : Type u} {β : Type v} {γ : Type w} {f : α → β}
    [add_comm_monoid β] [decidable_eq α] {s : finset γ} {t : γ → finset α} :
    ((s.1.bind (val ∘ t)).map f).sum = s.sum (λ (x : γ), sum (t x) f) := 
show ((s.1.bind (finset.val ∘ t)).map f).sum = (s.1.map (λ (x : γ), sum (t x) f)).sum, from
multiset.induction_on s.1 (by simp)
(assume x s ih, begin 
  unfold multiset.bind at *,
  rw [multiset.map_cons, multiset.join_cons, multiset.map_add, multiset.sum_add, 
      ih, multiset.map_cons, multiset.sum_cons],
  refl,
end)

-- TODO (Kenny?)
lemma generate_eq_span {R : Type*} [comm_ring R] (S : set R) : generate S = span S := 
set.eq_of_subset_of_subset (λ a H, H (span S) subset_span) (span_minimal (generate.is_ideal _) 
(subset_generate _))


section
variables {α : Type*} [rα : comm_ring α]
include rα

lemma inj_of_bla {β : Type*} [comm_ring β] {f : α → β} [hf : is_ring_hom f] (h : ∀ {x}, f x = 0 → x = 0) : function.injective f := 
λ x y hxy, by rw [← sub_eq_zero_iff_eq, ← is_ring_hom.map_sub f] at hxy;
  exact sub_eq_zero_iff_eq.1 (h hxy)

instance indexed_product.is_ring_hom {I : Type*} {f : I → Type*} [∀ i : I, comm_ring (f i)]
(g : α → Π i : I, f i) [rh : ∀ i : I, is_ring_hom (λ a : α, g a i)] : is_ring_hom g :=
{ map_add := λ x y, funext $ λ i, @is_ring_hom.map_add _ _ _ _ _ (rh i) x y,
  map_mul := λ x y, funext $ λ i, @is_ring_hom.map_mul _ _ _ _ _ (rh i) x y,
  map_one := funext $ λ i, @is_ring_hom.map_one _ _ _ _ _ (rh i) }
end

open finset

lemma thingy {α β : Type*} [ring α] [module α β] {s : finset β}
    {r : lc α β}
    (hr : (∀ x, x ∉ (↑s : set β) → r x = 0)) :
    finsupp.sum r (λ (b : β) (a : α), a • b) = s.sum (λ y, r y • y) :=
have h₁ : r.support ⊆ s := λ x hx, classical.by_contradiction 
  (λ h₁, ((finsupp.mem_support_iff r _).1 hx) (hr _ h₁)),
have h₂ : sum (s \ r.support) (λ y, r y • y) = 0 := begin
  rw ← @finset.sum_const_zero _ _ (s \ r.support),
  refine finset.sum_congr rfl _,
  assume x hx,
  rw [mem_sdiff, finsupp.mem_support_iff, ne.def, not_not] at hx,
  simp [hx.2],
end,
by rw [← finset.sum_sdiff h₁, h₂, zero_add]; refl

lemma span_finset {α β : Type*} {x : β} [ring α] [module α β] {s : finset β} 
    : x ∈ span (↑s : set β) ↔ ∃ r : β → α, s.sum (λ y, r y • y) = x :=
⟨λ ⟨r, hr⟩, ⟨r, by rw [← thingy hr.1, hr.2]⟩,
λ ⟨r, hr⟩, ⟨⟨s.filter (λ x, r x ≠ 0), 
  λ x, if x ∈ s then r x else 0, 
  λ a, ⟨λ h, by rw if_pos (mem_filter.1 h).1;exact (mem_filter.1 h).2,
     λ h, or.cases_on (classical.em (a ∈ s))
      (λ ha, mem_filter.2 (by rw if_pos ha at h; exact ⟨ha, h⟩))
      (λ ha, by rw if_neg ha at h; exact false.elim (h rfl))⟩⟩, 
  ⟨λ x hx, if_neg hx,
  show x = finsupp.sum _ (λ _ _, _ • _), begin 
  rw [@thingy _ _ _ _ s, ← hr],
    { exact finset.sum_congr rfl (λ y hy, 
        (show _ = ite _ _ _ • _, by rw if_pos hy)) },
    { assume x (hx : x ∉ s), 
      exact if_neg hx }
   end⟩ ⟩ ⟩

lemma span_image {α β γ : Type*} {x : β} [ring α] [module α β] {s : finset γ}
    {f : γ → β} : x ∈ span (↑(s.image f) : set β) ↔ 
    ∃ r : γ → α, x = s.sum (λ b, r b • f b) :=
⟨λ ⟨⟨supp, r, hs⟩, hr₁, hr₂⟩,
have hc : ∀ y ∈ s, ∃ z ∈ s, f z = f y := λ y hy, ⟨y, hy, rfl⟩,
let g := λ y, if ∃ hy : y ∈ s, y = some (hc y hy) then (r ∘ f) y else 0 in
let t := s.filter (λ y, ∃ hy : y ∈ s, y = some (hc y hy) ∧ r (f y) ≠ 0) in 
have h : sum (s \ t) (λ (y : γ), g y • f y) = 0 := begin
  conv {to_rhs, rw ← @sum_const_zero _ _ (s \ t)},
  refine sum_congr rfl (λ y (hy : y ∈ s \ filter _ _), _),
  show (ite _ _ _ • _ = _),
  rw [mem_sdiff, mem_filter, not_and] at hy,
  have := not_exists.1 (hy.2 hy.1) hy.1,
  cases classical.em (y = some (hc y hy.1)) with h h,
  { rw [not_and] at this, 
    have := this h,
    rw [ne.def, not_not] at this,
    rw [if_pos, function.comp_app, this, zero_smul],
    exact ⟨hy.1, h⟩ },
  { have : ¬∃ H : y ∈ s, y = some (hc y H) := λ ⟨_, hn⟩, h hn,
    rw [if_neg this, zero_smul] }
end,
have hg : ∀ y, ∀ hy : y ∈ s, g y ≠ 0 → 
    y = @classical.some γ (λ z, ∃ H : z ∈ s, f z = f y) (hc y hy) := 
  λ y hy (hy' : ite _ _ _ ≠ _),
  classical.by_contradiction (λ h,
  have h' : ¬ ∃ (h :y ∈ s), y = @classical.some γ (λ z, ∃ H : z ∈ s, f z = f y) (hc y hy) :=
    λ ⟨_, h'⟩, h h',
  by rw if_neg h' at hy'; exact false.elim (hy' rfl)),
have hy : ∀ y : γ, y ∈ s ∧ g y ≠ 0 → g y • f y = r (f y) • f y :=
  λ y (hy : _ ∧ ite _ _ _ ≠ _),
  show ite _ _ _ • _ = _, by 
  have := hg y hy.1 hy.2; rw if_pos at ⊢ hy; exact ⟨hy.1, this⟩,
⟨g, by rw [hr₂, ← sum_sdiff (filter_subset s : t ⊆ s), h, zero_add];
  exact eq.symm (sum_bij 
    (λ a _, f a) 
    (λ a ha, let ⟨_, _, _, ha⟩ := mem_filter.1 ha in
      (finsupp.mem_support_iff _ _).2 ha) 
    (λ a ha, 
      let ⟨_, has, hs, ha⟩ := mem_filter.1 ha in
      show ite _ _ _ • _ = _,
      by rw if_pos (⟨has, hs⟩ : (∃ (hy : a ∈ s), a = some _));
      refl)
    (λ a₁ a₂ ha₁ ha₂ haa,
    begin 
      rcases mem_filter.1 ha₁ with ⟨_, _, ha₁, _⟩,
      rcases mem_filter.1 ha₂ with ⟨_, _, ha₂, _⟩,
      rw [ha₁, ha₂],
      simp only [haa],
    end)
    (λ a ha, 
      have _ := mem_image.1 (not_imp_comm.1 (hr₁ a) 
        ((finsupp.mem_support_iff _ _).1 ha)),
      let ⟨hs₁, hs₂⟩ := some_spec this in
      ⟨some this, ⟨mem_filter.2 ⟨hs₁, hs₁, by simp only [hs₂], 
          hs₂.symm ▸ (hs a).1 ha⟩, hs₂.symm⟩⟩) ) ⟩,

λ ⟨r, hr⟩, hr.symm ▸ is_submodule.sum (λ c hc, is_submodule.smul _ 
    (subset_span (mem_image.2 ⟨c, hc, rfl⟩))) ⟩
 
lemma pow_thing {α R : Type*} [comm_ring R] (s : finset α)
    (f : α → R) (n : α → ℕ) (r : α → R) : s.sum (λ a, r a • f a) ^ (s.sum n + 1) ∈ span 
    (↑(s.image (λ a, f a ^ n a)) : set R) :=
finset.induction_on s (by simp) $ λ a s has hi, 
begin
  rw [sum_insert has, add_pow],
  refine @is_submodule.sum R R _ _ (span _) _ _ _ _ _ (λ k hk, _),
  cases le_total (n a) k with hak hak,
  { rw [← nat.add_sub_cancel' hak, pow_add],
    simp only [mul_assoc, smul_eq_mul, mul_pow, mul_left_comm _ (f a ^ n a)],
    exact is_submodule.smul' _ (subset_span (mem_image.2 ⟨a, mem_insert_self _ _, rfl⟩)) },
  { rw [sum_insert has, add_assoc, add_comm (n a), nat.add_sub_assoc hak, pow_add],
    simp only [mul_assoc, smul_eq_mul, mul_pow, mul_left_comm _ (sum s _ ^ (sum s n + 1))],
    have : span ↑(image (λ (a : α), f a ^ n a) s) ⊆ 
        span ↑(image (λ (a : α), f a ^ n a) (insert a s)) := 
      span_minimal is_submodule_span (set.subset.trans 
        (by rw [image_insert, coe_subseteq_coe]; exact subset_insert _ _) subset_span),
    refine is_submodule.smul' _ (this hi), }
end

lemma pow_generate_one_of_generate_one {α R : Type*} [comm_ring R] {s : finset α}
    {f : α → R} (n : α → ℕ) (h : (1 : R) ∈ span (↑(s.image f) : set R)) : 
    (1 : R) ∈ span (↑(s.image (λ x, f x ^ n x)) : set R) :=
let ⟨r, hr⟩ := span_image.1 h in
by rw [← one_pow (s.sum n + 1), hr];
  apply pow_thing

variables {R : Type*} {γ : Type*} [comm_ring R] [fintype γ]
open localization

private def α (f : γ → R) (x : R) : 
    Π i, loc R (powers (f i)) :=
  λ i, of_comm_ring R _ x

private noncomputable def β {f : γ → R}
    (r : Π i, loc R (powers (f i))) (j k : γ) :
    loc R (powers (f j * f k)) :=
localize_more_left (f j) (f k) (r j) - localize_more_right (f j) (f k) (r k)

lemma localize_more_left_eq (f g x : R) (n : ℕ) : 
    localize_more_left f g ⟦⟨x, ⟨f^n, n, rfl⟩⟩⟧ = ⟦⟨x * g^n, (f * g)^n, n, rfl⟩⟧ := begin
  let h,
  show ⟦_⟧ * classical.some h = ⟦_⟧,
  have := some_spec h,
  rw ← quotient.out_eq (some h) at *,
  rcases quotient.exact this with ⟨r, hr₁, hr₂⟩,
  refine quot.sound ⟨r, hr₁, _⟩,
  rw [sub_mul, sub_eq_zero_iff_eq] at hr₂,
  have hr₂' : ((out (some h)).snd).val * r = f ^ n * (out (some h)).fst * r :=
      by simpa using hr₂,
  suffices : (((out (some h)).snd).val * (x * g ^ n) 
      - ((f * g) ^ n * (x * (out (some h)).fst))) * r = 0,
    rw ← this, simp,
  simp only [sub_mul, mul_pow, mul_assoc, mul_left_comm (((out (some h)).snd).val), hr₂'],
  ring,
end

lemma localize_more_right_eq (f g x : R) (n : ℕ) : 
    localize_more_right f g ⟦⟨x, ⟨g^n, n, rfl⟩⟩⟧ = ⟦⟨x * f^n, (f * g)^n, n, rfl⟩⟧ := begin
  let h,
  show ⟦_⟧ * classical.some h = ⟦_⟧,
  have := some_spec h,
  rw ← quotient.out_eq (some h) at *,
  rcases quotient.exact this with ⟨r, hr₁, hr₂⟩,
  refine quot.sound ⟨r, hr₁, _⟩,
  rw [sub_mul, sub_eq_zero_iff_eq] at hr₂,
  have hr₂' : ((out (some h)).snd).val * r = g ^ n * (out (some h)).fst * r :=
      by simpa using hr₂,
  suffices : (((out (some h)).snd).val * (x * f ^ n) 
      - ((f * g) ^ n * (x * (out (some h)).fst))) * r = 0,
    rw ← this, simp,
  simp only [sub_mul, mul_pow, mul_assoc, mul_left_comm (((out (some h)).snd).val), hr₂'],
  ring,
end

lemma lemma_standard_covering₁ {f : γ → R}
    (h : (1 : R) ∈ span (↑(univ.image f) : set R)) : function.injective (α f) :=
@inj_of_bla _ _ _ _ (α f) (@indexed_product.is_ring_hom _ _ _ _ _ (α f) (λ i, by unfold α; apply_instance))
begin 
  assume x hx,
  replace hx := congr_fun hx,
  have : ∀ i, ∃ e : ℕ, f i ^ e * x = 0 := λ i, begin
    rcases (quotient.eq.1 (hx i)) with ⟨r, hr₁, hr₂⟩,
    cases hr₁ with e he,
    have : x * r = 0 := by simpa using hr₂,
    exact ⟨e, by rwa [mul_comm, he]⟩
  end,
  let e : γ → ℕ := λ i, classical.some (this i),
  have he : ∀ i, f i ^ e i * x = 0 := λ i, some_spec (this i),
  cases span_image.1 (pow_generate_one_of_generate_one e h) with r hr,
  rw [← one_mul x, hr, sum_mul, ← @sum_const_zero _ _ (univ : finset γ)],
  refine finset.sum_congr rfl (λ i _, _),
  rw [smul_eq_mul, mul_assoc, he, mul_zero],
end
 
lemma lemma_standard_covering₂ (f : γ → R) 
    (H : (1:R) ∈ span (↑(univ.image f) : set R)) (s : Π i, loc R (powers (f i))) :
    β s = 0 ↔ ∃ r : R, α f r = s := 
⟨λ h : β s = 0,
let t := λ i, out (s i) in
let r := λ i, some (t i).2.2 in
have hst : ∀ i, s i = ⟦⟨(t i).1, (f i) ^ (r i), r i, rfl⟩⟧ := 
    λ i, by simp [r, some_spec (t i).2.2],
have hi : ∀ i, s i = ⟦⟨(t i).1, (t i).2.1, (t i).2.2⟩⟧ := λ i, by simp,
have hβ : _ := λ i j, sub_eq_zero_iff_eq.1 $ show β s i j = 0, by rw h; refl,
have hβ : ∀ i j,
    (⟦⟨(t i).1 * f j ^ r i, ⟨(f i * f j) ^ r i, r i, rfl⟩⟩⟧ : loc R (powers (f i * f j))) =
    ⟦⟨(t j).1 * f i ^ r j, ⟨(f i * f j) ^ r j, r j, rfl⟩⟩⟧ := by conv at hβ in (_ = _) {rw [hst, hst,
      localize_more_left_eq, localize_more_right_eq] }; exact hβ,
have ∀ i j, ∃ n, 
    ((f i * f j) ^ r i * ((t j).1 * f i ^ r j) - 
    ((f i * f j) ^ r j * ((t i).1 * f j ^ r i)))
    * (f i * f j) ^ n = 0 :=
  λ i j, let ⟨t, ⟨n, hn⟩, hnt⟩ := quotient.exact (hβ i j) 
      in ⟨n, by rw hn; exact hnt⟩,
let n := λ i j, some (this i j) + r i + r j in
have hn : ∀ i j, (f i ^ r i * (t j).1 - 
    f j ^ r j * (t i).1) * (f i * f j) ^ n i j = 0 := 
  λ i j, by rw [← zero_mul (f i ^ r i), 
          ← zero_mul (f j ^ r j), ← some_spec (this i j)];
    simp [n, pow_add, mul_pow];
    ring,
let N := finset.sum (univ : finset (_ × _)) (λ ij, n ij.1 ij.2) in
have Nlt : ∀ i j, n i j ≤ N := λ i j, 
  @single_le_sum _ _ _ _ (λ h : γ × γ, n h.1 h.2)
  _ (λ _ _, nat.zero_le _) _ (mem_univ (i, j)),
have hN : ∀ i j, (f i ^ r i * (t j).1 - 
    f j ^ r j * (t i).1) * (f i * f j) ^ N = 0 := λ i j, 
  begin rw [← nat.sub_add_cancel (Nlt i j), 
      ← zero_mul ((f i * f j) ^ (N - n i j)), ← hn i j, 
      pow_add _ (N - n i j), mul_pow, mul_pow],
    simp [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc],
  end,
let ⟨a, ha⟩ := span_image.1 (pow_generate_one_of_generate_one (λ i, N + r i) H) in
⟨univ.sum (λ j, a j * (f j) ^ N * (t j).1),
funext (λ i, (hst i).symm ▸ quot.sound ⟨(f i) ^ N, ⟨N, rfl⟩,
have (λ j, f i ^ r i * (a j * f j ^ N * (t j).fst) * f i ^ N) =
      (λ j, (a j • (f j) ^ (N + r j) * (t i).1) * (f i) ^ N) := funext (λ j, begin
  rw [← sub_eq_zero_iff_eq, smul_eq_mul],
  simp only [mul_assoc, mul_left_comm _ (a j)],
  rw [← mul_sub],
  suffices : (f i ^ r i * (f j ^ N * ((t j).fst * f i ^ N))) -
      (f j ^ (N + r j) * ((t i).fst * f i ^ N)) = 0,
  { rw [this, mul_zero] },
  rw ← hN i j,
  simp [pow_add, mul_pow],
  ring,
  end),
begin
  suffices : ((t i).fst - (f i ^ r i * sum univ (λ j, a j * f j ^ N * (t j).1))) * f i ^ N = 0,
    simpa using this,
  rw [mul_sum, sub_mul, sum_mul, this, ← sum_mul, ← sum_mul, ← ha, one_mul, sub_self]
end⟩)⟩,
λ ⟨r, hr⟩, hr ▸ show β (α f r) = λ i j, 0, from funext $ λ i, funext $ λ j, 
  sub_eq_zero_iff_eq.2 $ loc_commutes _ _ _ ⟩
