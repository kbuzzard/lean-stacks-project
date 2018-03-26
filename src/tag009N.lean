/-
\begin{lemma}
\label{lemma-extend-off-basis}
Let $X$ be a topological space.
Let $\mathcal{B}$ be a basis for the topology on $X$.
Let $\mathcal{F}$ be a sheaf of sets on $\mathcal{B}$.
There exists a unique sheaf of sets $\mathcal{F}^{ext}$
on $X$ such that $\mathcal{F}^{ext}(U) = \mathcal{F}(U)$
for all $U \in \mathcal{B}$ compatibly with the restriction
mappings.
\end{lemma}

\begin{proof}
We first construct a presheaf $\mathcal{F}^{ext}$ with the
desired property. Namely, for an arbitrary open $U \subset X$ we
define $\mathcal{F}^{ext}(U)$ as the set of elements
$(s_x)_{x \in U}$ such that $(*)$ of
Lemma \ref{lemma-condition-star-sections} holds.
It is clear that there are restriction mappings
that turn $\mathcal{F}^{ext}$ into a presheaf of sets.
Also, by Lemma \ref{lemma-condition-star-sections} we
see that $\mathcal{F}(U) = \mathcal{F}^{ext}(U)$
whenever $U$ is an element of the basis $\mathcal{B}$.
To see $\mathcal{F}^{ext}$ is a sheaf one may
argue as in the proof of Lemma \ref{lemma-sheafification-sheaf}.
\end{proof}
-/

-- sheaf on a basis = sheaf on the whole space

import analysis.topology.topological_space tag009J tag009H scheme 

theorem basis_element_is_open {X : Type*} [T : topological_space X]
 {B : set (set X)} (HB : topological_space.is_topological_basis B)
 {U : set X} (BU : B U) : T.is_open U := 
 begin
 have : T = topological_space.generate_from B := HB.2.2,
 rw this,
show topological_space.generate_open B U,
refine topological_space.generate_open.basic U BU,
end 

 definition restriction_of_presheaf_to_basis {X : Type*} [T : topological_space X]
 {B : set (set X)} {HB : topological_space.is_topological_basis B}
 (FP : presheaf_of_types X) : presheaf_of_types_on_basis HB :=
 { F := λ U BU, FP.F U (basis_element_is_open HB BU),
   res := λ {U V} BU BV H, FP.res U V (basis_element_is_open HB BU) (basis_element_is_open HB BV) H,
   Hid := λ U BU, FP.Hid U (basis_element_is_open HB BU),
   Hcomp := λ U V W BU BV BW,FP.Hcomp U V W (basis_element_is_open HB BU)
   (basis_element_is_open HB BV) (basis_element_is_open HB BW)
 }

definition extend_off_basis {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB)
  : presheaf_of_types X := 
  { F := λ U OU,{ s : Π (x : U), presheaf_on_basis_stalk FB x // locally a section},
    res := _,
    Hid := _,
    Hcomp := _
  }

variables {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB)
#check HF

theorem extension_is_sheaf {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB)
  : is_sheaf_of_types (extend_off_basis FB HF) := sorry

definition extend_off_basis_map {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB) :
  morphism_of_presheaves_of_types_on_basis FB (restriction_of_presheaf_to_basis (extend_off_basis FB HF)) := sorry

theorem extension_extends {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB) : 
  is_isomorphism_of_presheaves_of_types_on_basis (extend_off_basis_map FB HF) := sorry 

theorem extension_unique {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB) (G : presheaf_of_types X)
  (HG : is_sheaf_of_types G) (psi : morphism_of_presheaves_of_types_on_basis FB (restriction_of_presheaf_to_basis G))
  (HI : is_isomorphism_of_presheaves_of_types_on_basis psi) -- we have an extension which agrees with FB on B
  : ∃ rho : morphism_of_presheaves_of_types (extend_off_basis FB HF) G, -- I would happily change the direction of the iso rho
    is_isomorphism_of_presheaves_of_types rho ∧ 
    ∀ (U : set X) (BU : B U), 
      (rho.morphism U (basis_element_is_open HB BU)) ∘ ((extend_off_basis_map FB HF).morphism U BU) = (psi.morphism U BU) := sorry


