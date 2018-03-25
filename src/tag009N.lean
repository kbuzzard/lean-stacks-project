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

import analysis.topology.topological_space tag009J scheme 

theorem basis_element_is_open {X : Type*} [T : topological_space X]
 {B : set (set X)} (HB : topological_space.is_topological_basis B)
 {U : set X} (BU : B U) : T.is_open U := sorry 

 definition restriction_of_presheaf_to_basis {X : Type*} [T : topological_space X]
 {B : set (set X)} {HB : topological_space.is_topological_basis B}
 (FP : presheaf_of_types X) : presheaf_of_types_on_basis HB :=
 { F := λ U BU, FP.F U (basis_element_is_open HB BU),
   res := λ {U V} BU BV H, FP.res U V (basis_element_is_open HB BU) (basis_element_is_open HB BV) H,
   Hid := λ U BU, FP.Hid U (basis_element_is_open HB BU),
   Hcomp := λ U V W BU BV BW,FP.Hcomp U V W (basis_element_is_open HB BU)
   (basis_element_is_open HB BV) (basis_element_is_open HB BW)
 }

definition extend_off_basis {X : Type*} [T : topological_space X] (B : set (set X)) 
  (HB : topological_space.is_topological_basis B) (FB : presheaf_of_types_on_basis HB)
  (HF : ∀ U BU (Ui : _ → set X) BUi Hcov Uijk BUijk Hcov2,
    is_sheaf_of_types_on_basis B HB FB U BU Ui BUi Hcov Uijk BUijk Hcov2)
  : ∃ FP : presheaf_of_types X,
  --  ∃ isom : Π U : set X, (∀ BU : B U, FB.F BU → FP.F U (basis_element_is_open BU),
