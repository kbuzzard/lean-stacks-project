/-
\begin{lemma}
\label{lemma-standard-covering}
Let $R$ be a ring, and let $f_1, f_2, \ldots f_n\in R$ generate
the unit ideal in $R$.
Then the following sequence is exact:
$$
0 \longrightarrow
R \longrightarrow
\bigoplus\nolimits_i R_{f_i} \longrightarrow
\bigoplus\nolimits_{i, j}R_{f_if_j}
$$
where the maps $\alpha : R \longrightarrow \bigoplus_i R_{f_i}$
and $\beta : \bigoplus_i R_{f_i} \longrightarrow \bigoplus_{i, j} R_{f_if_j}$
are defined as
$$
\alpha(x) = \left(\frac{x}{1}, \ldots, \frac{x}{1}\right)
\text{ and }
\beta\left(\frac{x_1}{f_1^{r_1}}, \ldots, \frac{x_n}{f_n^{r_n}}\right)
=
\left(\frac{x_i}{f_i^{r_i}}-\frac{x_j}{f_j^{r_j}}~\text{in}~R_{f_if_j}\right).
$$
\end{lemma}

\begin{proof}
We first show that $\alpha$ is injective,
and then that the image of $\alpha$ equals the kernel of $\beta$.
Assume there exists $x\in R$ such that $\alpha(x) = (0, \ldots, 0)$.
Then $\frac{x}{1} = 0$ in $R_{f_i}$ for all $i$.
This means, for all $i$, there exists a number $n_i$ such that
$$
f_i^{n_i}x = 0
$$
Since the $f_i$ generate $R$, we can pick $a_i$ so
$$
1 = \sum\nolimits_{i = 1}^n a_if_i
$$
Then for all $M\geq\sum n_i$, we have
$$
1^M = \left(\sum a_if_i\right)^M
= \sum {M \choose u_1, \ldots, u_n}
a_1^{u_1} a_2^{u_2} \ldots a_n^{u_n}
f_1^{u_1} f_2^{u_2} \ldots f_n^{u_n}
$$
where each term has a factor of at least $f_i^{n_i}$ for some $i$.
Therefore,
$$
x = 1x = 1^Mx = \left(\sum a_if_i\right)^Mx = 0.
$$
Thus, if $\alpha(x) = 0$, $x = 0$ and $\alpha$ is injective.
We check that the image of $\alpha$ equals the kernel of $\beta$.
First, note that for $x\in R$,
$$
\beta(\alpha(x)) =
\beta\left(\frac{x}{1}, \ldots, \frac{x}{1}\right) =
(\frac{x}{1}-\frac{x}{1}~in~R_{f_if_j}) = 0.
$$
Therefore, the image of $\alpha$ is in the kernel of $\beta$,
and it remains only to verify that if
$$
\beta\left(\frac{x_1}{f_1^{r_1}}, \ldots, \frac{x_n}{f_n^{r_n}}\right) = 0,
$$
then there exists $x\in R$ so that for all $i$,
$$
\frac{x}{1} = \frac{x_i}{f_i^{r_i}}
$$
Assume we have $x_1, \ldots, x_n$ such that
$$
\beta\left(\frac{x_1}{f_1^{r_1}}, \ldots, \frac{x_n}{f_n^{r_n}}\right) = 0.
$$
Then, for all pairs $i, j$, there exists an $n_{ij}$ such that
$$
f_i^{n_{ij}}f_j^{n_{ij}}(f_j^{r_j}x_i-f_i^{r_i}x_j) = 0
$$
Choosing $N$ so $N\geq n_{ij}$ for all $i, j$, we see that
$$
f_i^Nf_j^N(f_j^{r_j}x_i - f_i^{r_i}x_j) = 0
$$
Define elements $\widetilde{x_i}$ and $\widetilde{f_i}$ of $R$
as follows:
$$
\widetilde{f_i} = f_i^{N + r_i}, \quad \widetilde{x_i} = f_i^N x_i.
$$
Notice that
$$
\frac{\widetilde{x_i}}{\widetilde{f_i}} = \frac{x_i}{f_i^{r_i}}.
$$
Also, we can use this to rewrite the above equation
$f_i^Nf_j^N(f_j^{r_j}x_i - f_i^{r_i}x_j) = 0$ to get
the following equality, for all $i, j$,
$$
\widetilde{f_j}\widetilde{x_i} = \widetilde{f_i}\widetilde{x_j}.
$$
Since $f_1, \ldots, f_n$ generate $R$, we clearly have that
$\widetilde{f_1}, \ldots, \widetilde{f_n}$ also generate $R$.
Therefore, there exist $a_1, \ldots, a_n$ in $R$ so that
$$
1 = \sum\nolimits_{i = 1}^n a_i\widetilde{f_i}
$$
Therefore, we finally conclude that for all $i$,
$$
\frac{x_i}{f_i^{r_i}} =
\frac{\widetilde{x_i}}{\widetilde{f_i}} =
\sum\nolimits_{j = 1}^n
\frac{a_j\widetilde{f_j}\widetilde{x_i}}{\widetilde{f_i}} =
\sum\nolimits_{j = 1}^n
\frac{a_j\widetilde{f_i}\widetilde{x_j}}{\widetilde{f_i}} =
\frac{\sum_{j = 1}^na_j\widetilde{x_j}}{1}.
$$
Thus, we have
$$
\alpha\left(\sum\nolimits_{j = 1}^na_j\widetilde{x_j}\right) =
\left(\frac{x_1}{f_1^{r_1}}, \ldots, \frac{x_n}{f_n^{r_n}}\right),
$$
as required.  There the sequence is exact.
\end{proof}
-/

import Kenny_comm_alg.Zariski localization_UMP
import Kenny_comm_alg.ideal_operations
import massot_indexed_products
import data.fintype
import tactic.ring
import chris_ring_lemma
local attribute [instance] classical.prop_decidable

universe u

/- we no longer need this

theorem weak_binomial {R : Type u} [comm_ring R] (m n : nat) (x y : R) :
∃ f g : R, (x + y) ^ (m + n) = f * x ^ m + g * y ^ n := 
begin
  cases n with n1,
  { existsi (0:R),
    existsi (x+y)^m,
    simp
  },
  have H := is_ideal.some_binomial_theorem_boi x y m n1,
  existsi is_ideal.some_binomial_boi x y m n1 * x,
  existsi is_ideal.some_binomial_boi y x n1 m,
  conv in (m + nat.succ n1) {
  rw nat.succ_eq_add_one,
  rw ←add_assoc,
  },
  rw H,
--  conv in (is_ideal.some_binomial_boi x y m n1 * x * x ^ m) {
  rw mul_assoc,
  refl,
  end

-/

-- TODO (KB) Get chris proof in here. This will tell me how to use generate v span


-- Should we be using a list?
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

theorem missing3 {R : Type*} [comm_semiring R] (L : finset R) (e : R → ℕ) 
    (r : R → R) (s : R) : L ≠ ∅ → (∀ {f} (hfL : f ∈ L), f ^ (e f) * s = 0) →
    L.sum (λ x, r x * x) ^ L.sum e * s = 0 :=
finset.induction_on L (by simp) $ λ a L has hi _ hf, or.cases_on (classical.em (L = ∅)) 
(λ h, by simp [h, mul_pow, mul_assoc, hf (mem_insert_self a _)] ) $ λ h, begin
  rw [sum_insert has, sum_insert has, add_pow, sum_mul, ← @sum_const_zero _ _ (range (nat.succ (e a + sum L e)))],
  refine finset.sum_congr rfl (λ m hm, _),
  cases le_total m (e a) with hm' hm',
  { rw [add_comm (e a), nat.add_sub_assoc hm', pow_add],
    simp only [mul_assoc, mul_left_comm (sum L (λ (x : R), r x * x) ^ sum L e)],
    simp [hi h (λ f h, hf (mem_insert_of_mem h))] },
  { rw [← nat.add_sub_cancel' hm', pow_add, mul_pow],
    simp only [mul_assoc, mul_left_comm (a ^ e a)],
    simp [hf (mem_insert_self a _)] }
end

theorem missing4 {R : Type*} [comm_semiring R] (L : finset R) (e : R → ℕ)
    (r : R → R) (s : R) (hf : ∀ {f} (hfL : f ∈ L), f ^ (e f) * s = 0)
    (hL : L.sum (λ x, r x * x) = 1) : s = 0 :=
or.cases_on (classical.em (L = ∅)) (λ h, by simp [h] at *; rw [← mul_one s, ← hL, mul_zero]) $ λ h,
by have := missing3 L e r s h @hf;
  rwa [hL, one_pow, one_mul] at this

local notation f ` ∑ ` : 90 n : 90  := finset.sum (finset.range n) f

#print lc
#print finsupp



lemma multiset_span {α β : Type*} [ring α] [module α β] (s : finset β) (m : multiset β) :
    (∀ x ∈ m, ∃ y ∈ s, ∃ z, z • y = x) → m.sum ∈ span (↑s : set β) :=
multiset.induction_on m (λ _ , ⟨⟨∅, λ x, 0, λ a, by simp⟩, ⟨λ _ _, rfl, rfl⟩⟩) 
$ λ a m hi h, 
let ⟨r, hr⟩ := span_finset.1 (hi (λ x hx, h x (multiset.mem_cons_of_mem hx))) in
let ⟨y, hy, z, hz⟩ := h a (multiset.mem_cons_self _ _) in
span_finset.2 ⟨λ x, if x = y then r x + z else r x,
begin
  rw [multiset.sum_cons, ← hr, ← insert_erase hy, sum_insert (not_mem_erase _ _),
      sum_insert (not_mem_erase _ _), if_pos rfl, add_smul, hz, ← add_assoc, add_comm (r y • y)],
  refine congr_arg _ (finset.sum_congr rfl (λ x hx, _)),
  rw if_neg (mem_erase.1 hx).1,
end⟩

lemma multiset.sum_map_mul {α : Type u} {β : Type v} [_inst_1 : decidable_eq α] 
    {s : multiset α} {f : α → β} {b : β}
    [semiring β] : (s.map f).sum * b = (s.map (λ (x : α), f x * b)).sum :=
multiset.induction_on s (by simp) $ λ a s ih,
  by rw [multiset.map_cons, multiset.sum_cons, multiset.map_cons, multiset.sum_cons, ← ih, add_mul]

lemma multiset.map_id {α : Type u} (m : multiset α) : m.map id = m := 
multiset.induction_on m rfl (by simp [multiset.map_cons] {contextual := tt})

lemma multiset_thing {R : Type*} [comm_ring R] (s : finset R) (n : R → ℕ)
    (m : multiset R) :
    (∀ a ∈ m, ∃ m' : multiset R, (∀ x ∈ m', ∃ y ∈ s, ∃ z, z • (y ^ n y) = x) ∧ a = m'.sum) →
    ∃ l : multiset R, (∀ x ∈ l, ∃ y ∈ s, ∃ z, z • (y ^ n y) = x) ∧ 
    l.sum = m.sum := 
multiset.induction_on m (λ _, ⟨0, λ _ h, false.elim (multiset.not_mem_zero _ h), rfl⟩) 
$ λ a m ih hm, 
let ⟨ma, hma⟩ := hm a (multiset.mem_cons_self _ _) in
let ⟨mi, hmi⟩ := ih (λ a ha, hm a (multiset.mem_cons_of_mem ha)) in
⟨ma + mi, λ x hx, or.cases_on (multiset.mem_add.1 hx) (hma.1 _) (hmi.1 _),
by rw [multiset.sum_add, multiset.sum_cons, hmi.2, hma.2]⟩

lemma multiset_thing1 {R : Type*} [comm_ring R] (s : finset R) 
    (n : R → ℕ) (r : R → R) :
    s ≠ ∅ → ∃ m : multiset R, (∀ x ∈ m, ∃ y ∈ s, ∃ z, z • (y ^ n y) = x) ∧ 
    m.sum = s.sum (λ y, r y * y) ^ s.sum n :=
finset.induction_on s (λ h, false.elim (h rfl)) $ λ a s has hi _, 
or.cases_on (classical.em (s = ∅)) (λ h, ⟨r a ^ n a * a ^ n a :: 0, ⟨λ x hx, ⟨a, mem_insert_self _ _, r a ^ n a, 
by rw multiset.mem_singleton.1 hx; simp⟩, by simp [sum_insert has, h, mul_pow]⟩⟩) $ λ hs,
begin
  conv in (_ = _) { to_rhs, rw [sum_insert has, add_pow] },
  apply multiset_thing,
  assume b hbm,
  cases multiset.mem_map.1 hbm with k hk,
  cases le_total k (n a) with hk' hk',
  { rw [sum_insert has, add_comm (n a), nat.add_sub_assoc hk', pow_add] at hk,
    cases hi hs with w hw,
    existsi w.map (* ((r a * a) ^ k * sum s (λ (y : R), r y * y) ^ (n a - k)) *
        ↑(choose (sum s n + n a) k)),
    split,
    { assume x hx,
      cases multiset.mem_map.1 hx with p hp,
      rcases hw.1 p hp.1 with ⟨y, hy, z, hz⟩,
      existsi [y, mem_insert_of_mem hy, z * ((r a * a) ^ k * 
          sum s (λ (y : R), r y * y) ^ (n a - k) * ↑(choose (sum s n + n a) k))],
      rw [smul_eq_mul, mul_right_comm z, (show z * _ = _, from hz), hp.2] },
    { rw [← hk.2, ← hw.2, ← multiset.sum_map_mul, (show w.map (λ x, x) = w, from multiset.map_id w)],
      simp [mul_comm, mul_assoc, mul_left_comm] } },
  { rw [← nat.add_sub_cancel' hk', pow_add] at hk,
    existsi (b :: 0),
    exact ⟨λ x hx, ⟨a, mem_insert_self _ _, r a ^ n a *
      (r a * a) ^ (k - n a) * sum s (λ (y : R), r y * y) ^ 
      (sum (insert a s) n - (n a + (k - n a))) *
      ↑(choose (sum (insert a s) n) (n a + (k - n a))), 
        by rw [mem_singleton.1 hx, ← hk.2];
            simp [mul_comm, mul_left_comm, mul_assoc, mul_pow]⟩, 
        by simp [multiset.sum_cons]⟩ }
end

lemma pow_generate_one_of_generate_one {R : Type*} [comm_ring R] {L : finset R}
    (n : R → ℕ) (h : (1 : R) ∈ span (↑L : set R)) : 
    (1 : R) ∈ span (↑(image (λ x, x ^ n x) L) : set R) := 
let ⟨r, (hr : sum L (λ (y : R), _ * y) = 1)⟩ := span_finset.1 h in 
or.cases_on (classical.em (L = ∅)) (λ h, span_finset.2 ⟨r, by simpa [h] using hr⟩)
$ λ hL,
have hr' : (sum L (λ (y : R), r y * y)) ^ sum L n = 1 := by rw hr; simp,
let ⟨m, hm⟩ := multiset_thing1 L n r hL in
by rw [← hr', ← hm.2];
  exact multiset_span (image (λ x, x ^ n x) L) m 
  (λ x hx, let ⟨y, hy, z, hz⟩ := hm.1 x hx in 
    ⟨y ^ n y, mem_image.2 ⟨y, hy, rfl⟩, z, by rw hz⟩)

lemma span_image {α β γ : Type*} [ring α] [module α β] {s : finset γ} {f : γ → β}
    {x : β} (hs : x ∈ span (↑(s.image f) : set β)) : 
    ∃ r : γ → α, s.sum (λ y, r y • (f y)) = x :=
let ⟨r, hr⟩ := span_finset.1 hs in
have hc : ∀ y ∈ s, ∃ z ∈ s, f z = f y := λ y hy, ⟨y, hy, rfl⟩,
let g := λ y : γ, 
  if ∃ hy : y ∈ s, y = some (hc y hy) then (r ∘ f) y else 0 in 
let t := s.filter (λ y, ∃ hy : y ∈ s, y = some (hc y hy)) in
have h : sum (s \ t) (λ (y : γ), g y • f y) = 0 := begin
  conv {to_rhs, rw ← @sum_const_zero _ _ (s \ t)},
  refine sum_congr rfl (λ y (hy : y ∈ s \ filter _ _), _),
  show (ite _ _ _ • _ = _),
  rw [if_neg, zero_smul],
  { rw [mem_sdiff, mem_filter, not_and] at hy,
    exact hy.2 hy.1 } 
end,
have hg : ∀ y, ∀ hy : y ∈ s, g y ≠ 0 → 
    y = @classical.some γ (λ (z : γ), ∃ (H : z ∈ s), f z = f y) (hc y hy) := 
  λ y hy (hy' : ite _ _ _ ≠ _),
  classical.by_contradiction (λ h,
  have h' : ¬ ∃ (h :y ∈ s), y = @classical.some γ (λ (z : γ), ∃ (H : z ∈ s), f z = f y) (hc y hy) :=
    λ ⟨_, h'⟩, h h',
  by rw if_neg h' at hy'; exact false.elim (hy' rfl)),
have hy : ∀ y : γ, y ∈ s ∧ g y ≠ 0 → g y • f y = r (f y) • f y :=
  λ y (hy : _ ∧ ite _ _ _ ≠ _),
  show ite _ _ _ • _ = _, by  have := hg y hy.1 hy.2; rw if_pos at ⊢ hy; exact ⟨hy.1, this⟩,
⟨g,
by rw [← hr, ← sum_sdiff (filter_subset s : t ⊆ s), h, zero_add];
  exact sum_bij (λ y _, f y) 
    (λ y hy, mem_image.2 ⟨y, (mem_filter.1 hy).1, rfl⟩)
    (λ y hy', show ite _ _ _ • _ = _, 
      by rw mem_filter at hy'; rw if_pos hy'.2) 
    (λ a₁ a₂ ha₁ ha₂ h, begin 
      rw mem_filter at *,
      rcases ha₁ with ⟨_, ha₁, ha₁'⟩,
      rcases ha₂ with ⟨_, ha₂, ha₂'⟩,
      rw [ha₂', ha₁'],
      congr,
      simp [h],
      end) 
    (λ b hby, 
      let ⟨a, ha₁, ha₂⟩ := mem_image.1 hby in
      let ⟨hs₁, hs₂⟩ := some_spec (hc a ha₁) in
      ⟨some (hc a ha₁), mem_filter.2 ⟨hs₁, hs₁, by congr; simp only [hs₂]⟩,
      by rw [hs₂, ha₂] ⟩ ) ⟩

variables {R : Type*} [comm_ring R] (L : list R)
open localization
private def f (i : fin L.length) := list.nth_le L i.1 i.2

private def α (x : R) : Π i : fin L.length, loc R (powers (f L i)) :=
  λ i, of_comm_ring R _ x

private noncomputable def β (r : Π i : fin L.length, loc R (powers (f L i))) (j k : fin L.length) :
    loc R (powers (f L j * f L k)) :=
localize_more_left (f L j) (f L k) (r j) - localize_more_right (f L j) (f L k) (r k)

lemma localize_more_left_eq (f g x : R) (n : ℕ) : 
    localize_more_left f g ⟦⟨x, ⟨f^n, n, rfl⟩⟩⟧ = ⟦⟨x * g^n, (f * g)^n, n, rfl⟩⟧ := sorry

lemma localize_more_right_eq (f g x : R) (n : ℕ) : 
    localize_more_right f g ⟦⟨x, ⟨g^n, n, rfl⟩⟩⟧ = ⟦⟨x * f^n, (f * g)^n, n, rfl⟩⟧ := sorry

lemma lemma_standard_covering₁ {R : Type*} [comm_ring R] (L : list R) 
(H : (1:R) ∈ generate {x : R | x ∈ L}) : function.injective (@α R _ L) :=
@inj_of_bla _ _ _ _ (@α R _ L) (@indexed_product.is_ring_hom _ _ _ _ _ (@α R _ L) (λ i, by unfold α; apply_instance))
begin 
  assume x hx,
  replace hx := congr_fun hx,
  have : ∀ f' ∈ L, ∃ e : ℕ, f' ^ e * x = 0 := λ f' hf', begin
    have := hx ⟨list.index_of f' L, list.index_of_lt_length.2 hf'⟩,
    rcases (quotient.eq.1 this) with ⟨r, hr₁, hr₂⟩,
    cases hr₁ with e he,
    simp [f] at he hr₂,
    exact ⟨e, by rwa [mul_comm, he]⟩
  end,
  let e : R → ℕ := λ f', if h : f' ∈ L then classical.some (this f' h) else 0,
  have hL : {x : R | x ∈ L} = {x : R | x ∈ list.to_finset L} := set.ext (λ y, by simp),
  rw [generate_eq_span, hL] at H,
  cases span_finset.1 H with r hr,
  have he : ∀ f' : R, f' ∈ list.to_finset L → f' ^ e f' * x = 0 := λ f' hf,
    by rw list.mem_to_finset at hf;
    simp only [e, dif_pos hf];
    exact some_spec (this f' hf),
  exact missing4 (list.to_finset L) e r x he hr
end

lemma lemma_standard_convering₂ {R : Type*} [comm_ring R] (L : list R) 
    (H : (1:R) ∈ span {x | x ∈ L}) (s : Π i : fin L.length, loc R (powers (f L i))) :
    β L s = 0 ↔ ∃ r : R, α L r = s := 
⟨λ h,
let t := λ i, out (s i) in
let r := λ i, some (t i).2.2 in
have hst : ∀ i, s i = ⟦⟨(t i).1, (f L i) ^ (r i), r i, rfl⟩⟧ := 
    λ i, by simp [r, some_spec (t i).2.2],
have hi : ∀ i, s i = ⟦⟨(t i).1, (t i).2.1, (t i).2.2⟩⟧ := λ i, by simp,
have hβ : _ := λ i j, sub_eq_zero_iff_eq.1 $ show β L s i j = 0, by rw h; refl,
have hL' : (1 : R) ∈ span (↑(L.to_finset) : set R) := 
    by rwa (set.ext (λ x, show x ∈ (↑(L.to_finset) : set R) ↔ x ∈ L, from list.mem_to_finset)),
begin
  conv at hβ in (_ = _) {rw [hst, hst,
      localize_more_left_eq, localize_more_right_eq] },
  have : ∀ i j, ∃ n, 
        ((f L i * f L j) ^ r i * ((t j).1 * f L i ^ r j) - 
        ((f L i * f L j) ^ r j * ((t i).1 * f L j ^ r i)))
        * (f L i * f L j) ^ n = 0 :=
    λ i j, let ⟨t, ⟨n, hn⟩, hnt⟩ := quotient.exact (hβ i j) 
        in ⟨n, by rw hn; exact hnt⟩,
  let n := λ i j, some (this i j) + r i + r j,
  have hn : ∀ i j, (f L i ^ r i * (t j).1 - 
      f L j ^ r j * (t i).1) * (f L i * f L j) ^ n i j = 0 := 
    λ i j, by rw [← zero_mul (f L i ^ r i), 
            ← zero_mul (f L j ^ r j), ← some_spec (this i j)];
      simp [n, pow_add, mul_pow];
      ring,
  let N := finset.sum (univ : finset (_ × _)) (λ ij, n ij.1 ij.2),
  have Nlt : ∀ i j, n i j ≤ N := λ i j, 
      @single_le_sum _ _ _ _ (λ h : fin L.length × fin L.length, n h.1 h.2)
      _ (λ _ _, nat.zero_le _) _ (mem_univ (i, j)),
  have hN : ∀ i j, (f L i ^ r i * (t j).1 - 
      f L j ^ r j * (t i).1) * (f L i * f L j) ^ N = 0 := λ i j, 
    begin rw [← nat.sub_add_cancel (Nlt i j), 
        ← zero_mul ((f L i * f L j) ^ (N - n i j)), ← hn i j, 
        pow_add _ (N - n i j), mul_pow, mul_pow],
      simp [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc],
    end,
  let n' : R → ℕ := λ x, dite (∃ i, x = f L i) (λ hx, N + r (some hx)) (λ _, 0),
  rcases span_image (pow_generate_one_of_generate_one n' hL') with ⟨a, ha⟩,
  existsi ((univ : finset (fin L.length)).sum (λ i, a (f L i) * (t i).1 ^ (n' (f L i)))),
  refine funext (λ j, _),
  rw hst,
  refine quot.sound _,
  existsi [(1 : R), (⟨0, rfl⟩ : 1 ∈ powers (f L j))],
  simp,
end,
λ ⟨r, hr⟩, hr ▸ show β L (α L r) = λ i j, 0, from funext $ λ i, funext $ λ j, 
  sub_eq_zero_iff_eq.2 $ loc_commutes _ _ _ ⟩


#print finsupp
-- in chris_ring_lemma.lean there is
-- theorem missing1 [comm_semiring R] (n : ℕ) (f : ℕ → R) (e : ℕ → ℕ) (r : ℕ → R)
--     (s : R) : (∀ i : ℕ, i < n → (f i) ^ (e i) * s = 0) → 
--     sum (range n) (λ i, f i * r i) = 1 → s = 0 

/-
#check @or.rec -- dammit, or only eliminates to prop
open finset
example (R : Type) [comm_ring R] (n : ℕ) (a : fin n → R) (e : fin n → ℕ)
(r : R) (H : ∀ i : fin n, (a i) ^ (e i) * r = 0) :
(sum (univ) a) ^ (sum (univ) e) * r = 0 := missing1 n (λ i, or.elim (decidable.em (i < n)) (λ h, a ⟨i,h⟩) (λ h, 0))
(λ i, _) (λ i, _) _ r _

KB was working on this but now I have to do admin
-/
