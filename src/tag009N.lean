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

import analysis.topology.topological_space
#check topological_space.is_topological_basis_of_open_of_nhds

definition extend_off_basis {X : Type*} [T : topological_space X] (B : set (set X)) 
  (HB : topological_space.is_topological_basis B) (P : sheaf_of_sets_on_basis )