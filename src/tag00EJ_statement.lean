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
import chris_ring_lemma
import data.fintype
import tactic.ring
local attribute [instance] classical.prop_decidable

universe u
local infix ` ^ ` := monoid.pow 

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
open finset nat classical quotient

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

lemma span_finset {α β : Type*} {x : β} [ring α] [module α β] {s : finset β} 
    (h : x ∈ span {x : β | x ∈ s}) : ∃ r : β → α, s.sum (λ y, r y • y) = x :=
let ⟨r, hr⟩ := h in
have h₁ : r.support ⊆ s := λ x hx, classical.by_contradiction 
  (λ h₁, ((finsupp.mem_support_iff r _).1 hx) (hr.1 _ h₁)),
have h₂ : sum (s \ r.support) (λ y, r y • y) = 0 := begin 
  rw ← @finset.sum_const_zero _ _ (s \ r.support),
  refine finset.sum_congr rfl _,
  assume x hx,
  rw [mem_sdiff, finsupp.mem_support_iff, ne.def, not_not] at hx,
  simp [hx.2],
end,
⟨r, by rw [hr.2, ← finset.sum_sdiff h₁, h₂, zero_add]; refl⟩

theorem missing3 {R : Type*} [comm_semiring R] (L : finset R) (e : R → ℕ) 
    (r : R → R) (s : R) : L ≠ ∅ → (∀ {f} (hfL : f ∈ L), f ^ (e f) * s = 0) →
    L.sum (λ x, r x * x) ^ L.sum e * s = 0 :=
finset.induction_on L (by simp) $ λ a L has hi _ hf, or.by_cases (classical.em (L = ∅)) 
(λ h, by simp [h, mul_pow, mul_assoc, hf (mem_insert_self a _)]) $ λ h, begin
  rw [sum_insert has, sum_insert has, add_pow, sum_mul, ← @sum_const_zero _ _ (range (nat.succ (e a + sum L e)))],
  refine finset.sum_congr rfl (λ m hm, _),
  cases le_total m (e a) with hm' hm',
  { rw [add_comm (e a), nat.add_sub_assoc hm', _root_.pow_add],
    simp only [mul_assoc, mul_left_comm (sum L (λ (x : R), r x * x) ^ sum L e)],
    simp [hi h (λ f h, hf (mem_insert_of_mem h))] },
  { rw [← nat.add_sub_cancel' hm', _root_.pow_add, mul_pow],
    simp only [mul_assoc, mul_left_comm (a ^ e a)],
    simp [hf (mem_insert_self a _)] }
end

theorem missing4 {R : Type*} [comm_semiring R] (L : finset R) (e : R → ℕ)
    (r : R → R) (s : R) (hf : ∀ {f} (hfL : f ∈ L), f ^ (e f) * s = 0)
    (hL : L.sum (λ x, r x * x) = 1) : s = 0 :=
or.by_cases (classical.em (L = ∅)) (λ h, by simp [h] at *; rw [← mul_one s, ← hL, mul_zero]) $ λ h,
by have := missing3 L e r s h @hf;
  rwa [hL, one_pow, one_mul] at this

variables {R : Type*} [comm_ring R] (L : list R)
open localization
private def f (i : fin L.length) := list.nth_le L i.1 i.2

private def α (x : R) : Π i : fin L.length, loc R (powers (f L i)) :=
  λ i, of_comm_ring R _ x

private noncomputable def β (r : Π i : fin L.length, loc R (powers (f L i))) (j k : fin L.length) :
    loc R (powers (f L j * f L k)) :=
localize_more_left (f L j) (f L k) (r j) - localize_more_right (f L j) (f L k) (r k)

lemma lemma_00EJ_missing (r : R) (j k : fin L.length) : localize_more_left (f L j) (f L k) (of_comm_ring R (powers (f L j)) r) =
    localize_more_right (f L j) (f L k) (of_comm_ring R (powers (f L k)) r) := sorry

#check lemma_00EJ_missing
#print quotient.out
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
  cases span_finset H with r hr,
  have he : ∀ f' : R, f' ∈ list.to_finset L → f' ^ e f' * x = 0 := λ f' hf,
    by rw list.mem_to_finset at hf;
    simp only [e, dif_pos hf];
    exact some_spec (this f' hf),
  exact missing4 (list.to_finset L) e r x he hr
end

lemma lemma_standard_convering₂ {R : Type*} [comm_ring R] (L : list R) 
    (H : (1:R) ∈ generate {x : R | x ∈ L}) (s : Π i : fin L.length, loc R (powers (f L i))) :
    β L s = 0 ↔ ∃ r : R, α L r = s := 
⟨λ h,
  let t := λ i, ⟦out (s i)⟧ in
  have hst : s = t := by simp [t, out_eq],
begin
  rw hst at *,
  have hβ : ∀ i j, ⟦((out (s i)).fst, _)⟧ * _ = ⟦((out (s j)).fst, _)⟧ * _ := 
    λ i j, sub_eq_zero_iff_eq.1 $ show β L t i j = 0, by rw h; refl,
  conv at hβ in (_ = _) {rw ← out_eq (classical.some _),
    to_rhs, rw ← out_eq (classical.some _) },
  have := λ i j, quotient.exact (hβ i j),
  simp at this,
  unfold has_equiv.equiv setoid.r r at this,
  simp [(mul_add _ _ _).symm ] at this,

end,
λ ⟨r, hr⟩, hr ▸ show β L (α L r) = λ i j, 0, from funext $ λ i, funext $ λ j, 
  sub_eq_zero_iff_eq.2 $ loc_commutes _ _ _ ⟩


#print extend_map_of_im_unit._match_1
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
