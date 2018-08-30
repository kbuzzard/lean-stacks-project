import Kenny_comm_alg.ideal_lattice

noncomputable theory
local attribute [instance] classical.prop_decidable

universe u

namespace is_ideal

section avoid_powers

parameters {α : Type u} [comm_ring α]
parameters (f : α) (P : set α) [hp : is_ideal P]
parameters (hf : ∀ n : ℕ, f^n ∉ P)
include hp hf

private def avoid_powers_aux :
  ∃ (M : {S : set α // is_ideal S ∧ P ⊆ S ∧ ∀ n, f ^ n ∉ S}),
  ∀ x, M ≤ x → x = M :=
@@zorn.zorn' {S // is_ideal S ∧ P ⊆ S ∧ ∀ n, f^n ∉ S} _ ⟨⟨P, hp, set.subset.refl P, hf⟩⟩ $
λ c x hx hc, ⟨⟨{y | ∃ S : {S // is_ideal S ∧ P ⊆ S ∧ ∀ n, f^n ∉ S}, S ∈ c ∧ y ∈ S.val},
  { zero_ := ⟨x, hx, @@is_ideal.zero _ x.1 x.2.1⟩,
    add_  := λ x y ⟨Sx, hxc, hx⟩ ⟨Sy, hyc, hy⟩,
      or.cases_on (hc Sx Sy hxc hyc)
        (λ hxy, ⟨Sy, hyc, @@is_ideal.add _ Sy.2.1 (hxy hx) hy⟩)
        (λ hyx, ⟨Sx, hxc, @@is_ideal.add _ Sx.2.1 hx (hyx hy)⟩),
    smul  := λ x y ⟨Sy, hyc, hy⟩,
      ⟨Sy, hyc, @@is_ideal.mul_left _ Sy.2.1 hy⟩ },
  λ z hz, ⟨x, hx, x.2.2.1 hz⟩,
  λ n ⟨S, hsc, hfns⟩, S.2.2.2 n hfns⟩,
λ S hsc z hzs, ⟨S, hsc, hzs⟩⟩

def avoid_powers : set α :=
(classical.some avoid_powers_aux).1

theorem avoid_powers.contains : P ⊆ avoid_powers :=
(classical.some avoid_powers_aux).2.2.1

theorem avoid_powers.avoid_powers : ∀ n : ℕ, f^n ∉ avoid_powers :=
(classical.some avoid_powers_aux).2.2.2

def avoid_powers.is_prime_ideal : is_prime_ideal avoid_powers :=
{ ne_univ := λ h,
    have h1 : (1:α) ∈ (set.univ:set α), from show true, by trivial,
    have h2 : (1:α) ∈ avoid_powers, by rwa h,
    avoid_powers.avoid_powers 0 h2,
  mem_or_mem_of_mul_mem := λ x y hxy,
    have h1 : ∀ x, classical.some avoid_powers_aux ≤ x → x = classical.some avoid_powers_aux,
      from classical.some_spec avoid_powers_aux,
    have hax : avoid_powers ⊆ span (insert x avoid_powers),
      from set.subset.trans (set.subset_insert x _) subset_span,
    have hay : avoid_powers ⊆ span (insert y avoid_powers),
      from set.subset.trans (set.subset_insert y _) subset_span,
    have hax2 : P ⊆ span (insert x avoid_powers),
      from set.subset.trans avoid_powers.contains hax,
    have hay2 : P ⊆ span (insert y avoid_powers),
      from set.subset.trans avoid_powers.contains hay,
    have hnx : (¬∃ n, f^n ∈ span (insert x avoid_powers)) → x ∈ avoid_powers,
      from λ h,
      have h2 : _ := h1 ⟨_, is_ideal_span, hax2, λ n hnfs, h ⟨n, hnfs⟩⟩ hax,
      suffices x ∈ span (insert x avoid_powers),
        by unfold avoid_powers; rw ← h2; exact this,
      subset_span $ set.mem_insert x _,
    have hny : (¬∃ n, f^n ∈ span (insert y avoid_powers)) → y ∈ avoid_powers,
      from λ h,
      have h2 : _ := h1 ⟨_, is_ideal_span, hay2, λ n hnfs, h ⟨n, hnfs⟩⟩ hay,
      suffices y ∈ span (insert y avoid_powers),
        by unfold avoid_powers; rw ← h2; exact this,
      subset_span $ set.mem_insert y _,
    begin
      haveI ha : is_submodule (avoid_powers f P hf) :=
        (classical.some (avoid_powers_aux f P hf)).2.1.to_is_submodule,
      by_cases hx : ∃ m : ℕ, f^m ∈ span (insert x (avoid_powers f P hf)),
      { by_cases hy : ∃ n : ℕ, f^n ∈ span (insert y (avoid_powers f P hf)),
        { exfalso,
          cases hx with m hx,
          cases hy with n hy,
          rw span_insert at hx hy,
          rcases hx with ⟨x1, x2, hx2, hx⟩,
          rcases hy with ⟨y1, y2, hy2, hy⟩,
          haveI ha : is_submodule (avoid_powers f P hf) :=
            (classical.some (avoid_powers_aux f P hf)).2.1.to_is_submodule,
          rw span_eq_of_is_submodule ha at hx2 hy2,
          apply avoid_powers.avoid_powers f P hf (m+n),
          exact calc
          f ^ (m + n) = (x1 • x + x2) * (y1 • y + y2) : by rw [pow_add, hx, hy]
                  ... = (x1 * x + x2) * (y1 * y + y2) : rfl
                  ... = (x1 * y1) * (x * y) + (x1 * x) * y2 + (y1 * y) * x2 + x2 * y2 : by ring
                  ... ∈ avoid_powers f P hf :
            is_submodule.add
              (is_submodule.add
                 (is_submodule.add
                    (is_submodule.smul _ hxy)
                    (is_submodule.smul _ hy2))
                 (is_submodule.smul _ hx2))
              (is_submodule.smul _ hy2) },
        { right,
          exact hny hy } },
      { left,
        exact hnx hx }
    end,
  .. (classical.some avoid_powers_aux).2.1 }

end avoid_powers

end is_ideal