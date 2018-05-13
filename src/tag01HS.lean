/-
Tag 01HS

Lemma 25.5.1. Let R be a ring. Let f∈R.

    If g∈R and D(g)⊂D(f), then
        f is invertible in Rg,
        ge=af for some e≥1 and a∈R,
        there is a canonical ring map Rf→Rg, and
        there is a canonical Rf-module map Mf→Mg for any R-module M. 
    Any open covering of D(f) can be refined to a finite open covering of the form D(f)=⋃ni=1D(gi).
    If g1,…,gn∈R, then D(f)⊂⋃D(gi) if and only if g1,…,gn generate the unit ideal in Rf. 

Proof. Recall that D(g)=Spec(Rg) (see tag 00E4). Thus (a) holds because f maps to an element of Rg which
 is not contained in any prime ideal, and hence invertible, see tag 00E0. Write the inverse of f in Rg as a/gd.
 This means gd−af is annihilated by a power of g, whence (b). For (c), the map Rf→Rg exists by (a) from the
 universal property of localization, or we can define it by mapping b/fn to anb/gne. The equality Mf=M⊗RRf can be used to obtain the map on modules, or we can define Mf→Mg by mapping x/fn to anx/gne.

Recall that D(f) is quasi-compact, see tag 00F6. Hence the second statement follows directly from the fact that the standard opens form a basis for the topology.

The third statement follows directly from tag 00E0. 
-/

import Kenny_comm_alg.Zariski localization_UMP
import tensor_product 
import tag00E2 
import tag00E4
import tag00E8 -- Spec(R) is compact
import Kenny_comm_alg.avoid_powers algebra.module
import mathlib_someday.topology

universes u v

local attribute [instance] classical.prop_decidable

-- the next line should not be here. It's in broken Atiyah.lean.
-- KB added it to localization_UMP in localization namespace

--def is_unit {α : Type u} [comm_ring α] (x : α) := ∃ y, x * y = 1 

--localization.of_comm_ring :
--  Π (α : Type u_1) [_inst_1 : comm_ring α] (S : set α) [_inst_2 : is_submonoid α S], α → localization.loc α S

example (R : Type u) [comm_ring R] (f : R) : topological_space (X R) := by apply_instance 

/-- Stacks project tag 01HS -/
lemma lemma_standard_open_1b (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) :
  ∃ e : ℕ, ∃ a, g^e = a*f :=
have h1 : ¬∀ n, g^n ∉ span {f},
from λ h,
  let P := @@is_ideal.avoid_powers _ g (span {f}) is_ideal_span h in
  have h1 : ∀ n : ℕ, g ^ n ∉ P,
    from @@is_ideal.avoid_powers.avoid_powers _ g (span {f}) is_ideal_span h,
  have h2 : span {f} ⊆ P,
    from @is_ideal.avoid_powers.contains _ _ g (span {f}) is_ideal_span h,
  have h3 : is_prime_ideal P,
    from @@is_ideal.avoid_powers.is_prime_ideal _ g (span {f}) is_ideal_span h,
  have h4 : (⟨P, h3⟩ : X R) ∈ Spec.D' g,
    from λ h5, h1 1 $ by simpa [monoid.pow] using h5,
  H h4 $ h2 $ subset_span $ set.mem_singleton f,
begin
  simp [not_forall, span, span_singleton] at h1,
  rcases h1 with ⟨e, a, h⟩,
  exact ⟨e, a, h.symm⟩
end

lemma lemma_standard_open_1a (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) :
  localization.is_unit (localization.of_comm_ring R (powers g) f) :=
let ⟨e, a, h⟩ := lemma_standard_open_1b R f g H in
⟨⟦(a,(⟨g^e,⟨e,rfl⟩⟩:powers g))⟧,
 quotient.sound $ ⟨(1:R), ⟨0, rfl⟩, by simp [h, mul_comm]⟩⟩

noncomputable def lemma_standard_open_1c (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) :
  localization.away f → localization.away g :=
localization.away.extend_map_of_im_unit
  (localization.of_comm_ring R (powers g))
  (lemma_standard_open_1a R f g H) -- regardless of my incompetence above, I now need that
  -- if p:R->S is a ring hom and image of f is a unit then there's a unique q:R[1/f]->S
  -- such that p is q ∘ localization.of_comm_ring . Do we have this?

  -- Note that this lemma should have a uniqueness statement too, saying that there is precisely
  -- one R-algebra morphism between these rings. The uniqueness is essential because we want
  -- define O_X(U) to be R[1/f] if U=D(f), however this is not well-defined, so I propose
  -- defining it as the subring of the product (over all f such that )

instance lemma_standard_open_1c.is_ring_hom (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) :
  is_ring_hom (lemma_standard_open_1c R f g H) :=
localization.away.extend_map_of_im_unit.is_ring_hom _ _

local attribute [instance] is_ring_hom.to_module

set_option eqn_compiler.zeta true
def lemma_standard_open_1c.is_linear_map (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) :
  is_linear_map (lemma_standard_open_1c R f g H) :=
{ add := λ x y, is_ring_hom.map_add _,
  smul := λ c x, calc
          lemma_standard_open_1c R f g H (localization.of_comm_ring R _ c * x)
        = lemma_standard_open_1c R f g H (localization.of_comm_ring R _ c) * lemma_standard_open_1c R f g H x : is_ring_hom.map_mul _
    ... = localization.of_comm_ring R _ c * lemma_standard_open_1c R f g H x : congr_arg (λ z, z * lemma_standard_open_1c R f g H x) (localization.away.extend_map_extends _ _ _) }

noncomputable def lemma_standard_open_1d (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f))
  (M : Type) [module R M] :
  tensor_product M (localization.loc R (powers f)) → tensor_product M (localization.loc R (powers g)) :=
tensor_product.tprod_map
  is_linear_map.id
  (lemma_standard_open_1c.is_linear_map R f g H)

def lemma_standard_open_2 (R : Type u) [comm_ring R] (f : R) (α : Type v) 
  (cover : α → set (X R)) (Hcover : ∀ i : α, topological_space.is_open (Zariski R) (cover i)) : 
  set.Union cover = Spec.D'(f) → ∃ γ : Type v, ∃ refine : γ → α, ∃ g : γ → R,
  ∃ H : fintype γ, (∀ m : γ, Spec.D'(g m) ⊆ cover (refine m)) ∧ set.Union (λ m, Spec.D'(g m)) = Spec.D'(f)  
   := 

begin
  intro cover_covers,
  let Rf := localization.away f, -- R[1/f]
  have H1 : compact (@set.univ (X Rf)) := lemma_quasi_compact,
  let g := localization.of_comm_ring R (powers f),
  let φ := Zariski.induced g,
--   in
--  topological_space.open_immersion φ ∧ φ '' set.univ = Spec.D'(f) :=
  have H2 : compact (Spec.D' f),
    rw (lemma_standard_open R f).2.symm,
    exact compact_image H1 (Zariski.induced.continuous g),
  -- now refine cover to be a cover by basis elements
  -- first a bunch of axiom of choice nonsense
  let basis_cover := λ (i : α), classical.some (topological_space.Union_basis_elements_of_open (D_f_form_basis R) (Hcover i)),
  have basis_cover_proof : ∀ (i : α),
    (∃ (f : (basis_cover i) → set (X R)), cover i = set.Union f ∧ ∀ (i : (basis_cover i)), f i ∈ standard_basis R)
  := λ (i : α), classical.some_spec (topological_space.Union_basis_elements_of_open (D_f_form_basis R) (Hcover i)),
  let β := Σ (i : α), basis_cover i,
  let basis_cover_proof_function := λ i, classical.some (basis_cover_proof i),
  have basis_cover_proof_proof : ∀ (i : α),
  (cover i = set.Union (basis_cover_proof_function i)) ∧ (∀ (j : basis_cover i), (basis_cover_proof_function i) j ∈ standard_basis R)
  := λ i, classical.some_spec (basis_cover_proof i),

  let cover' : β → set (X R) := λ ⟨i,Hi⟩,basis_cover_proof_function i Hi, 
  -- claim that cover' is a cover
  have Hcover' : set.Union cover' = Spec.D' f,
    rw set.subset.antisymm_iff,
    split,
    { intros b Hb,
      cases Hb with V HV,cases HV with HV Hb,cases HV with j Hj,
      have Htemp := (basis_cover_proof_proof j.1).1,
      -- ready for proof now
      rw ←cover_covers,
      apply set.subset_Union cover j.fst,
      rw Htemp,
      apply set.subset_Union (basis_cover_proof_function j.1) j.2,
      suffices : basis_cover_proof_function (j.fst) (j.snd) = cover' j,
        rwa [this,←Hj],
      -- gaargh
      show basis_cover_proof_function (j.fst) (j.snd) = (λ ⟨i,Hi⟩,basis_cover_proof_function i Hi) j,
      
      
      sorry
    },
    { sorry},
  -- and we now need a lemma that says that any open is a union of basis elements
  -- then we build beta as a sigma type
  -- and beta has a map to alpha
  -- and then compactness gives a finite subcover gamma
  sorry  
end 
#check compact_image
#check D_f_form_basis
#print topological_space.is_topological_basis

-- proof goes "it's compact"

/-
--def lemma_standard_open_3 (R : Type u) [comm_ring R] (f : R) (g : list R) :
--  Spec.D'(f) ⊆ list.foldl (λ U r, set.union U (Spec.D'(r))) ∅ g ↔ "span of image of g in localization.of_comm_ring R (powers f) is whole ring" := sorry 
-/

#check embedding 
