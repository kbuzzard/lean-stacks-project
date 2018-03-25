/-
\begin{lemma}
\label{lemma-cofinal-systems-coverings}
With notation as above.
For each $U \in \mathcal{B}$, let $C(U) \subset \text{Cov}_\mathcal{B}(U)$
be a cofinal system. For each $U \in \mathcal{B}$, and each
$\mathcal{U} : U = \bigcup U_i$ in $C(U)$, let coverings
$\mathcal{U}_{ij} : U_i \cap U_j = \bigcup U_{ijk}$,
$U_{ijk} \in \mathcal{B}$ be given.
Let $\mathcal{F}$ be a presheaf of sets on $\mathcal{B}$.
The following are equivalent
\begin{enumerate}
\item The presheaf $\mathcal{F}$ is a sheaf on $\mathcal{B}$.
\item For every $U \in \mathcal{B}$ and every covering
$\mathcal{U} : U = \bigcup U_i$ in $C(U)$ the sheaf condition
$(**)$ holds (for the given coverings $\mathcal{U}_{ij}$).
\end{enumerate}
\end{lemma}

\begin{proof}
We have to show that (2) implies (1).
Suppose that $U \in \mathcal{B}$, and that
$\mathcal{U} : U = \bigcup_{i\in I} U_i$ is an arbitrary covering
by elements of $\mathcal{B}$.  Because the system $C(U)$ is cofinal
we can find an element $\mathcal{V} : U = \bigcup_{j \in J} V_j$
in $C(U)$ which refines $\mathcal{U}$. This means there exists
a map $\alpha : J \to I$ such that $V_j \subset U_{\alpha(j)}$.

\medskip\noindent
Note that if $s, s' \in \mathcal{F}(U)$ are sections such
that $s|_{U_i} = s'|_{U_i}$, then
$$
s|_{V_j}
= (s|_{U_{\alpha(j)}})|_{V_j}
= (s'|_{U_{\alpha(j)}})|_{V_j}
= s'|_{V_j}
$$
for all $j$. Hence by the uniqueness in $(**)$
for the covering $\mathcal{V}$ we conclude that $s = s'$.
Thus we have proved the uniqueness part of $(**)$
for our arbitrary covering $\mathcal{U}$.

\medskip\noindent
Suppose furthermore that $U_i \cap U_{i'} = \bigcup_{k \in I_{ii'}} U_{ii'k}$
are arbitrary coverings by $U_{ii'k} \in \mathcal{B}$.
Let us try to prove the existence part of $(**)$ for the system
$(\mathcal{U}, \mathcal{U}_{ij})$. Thus let $s_i \in \mathcal{F}(U_i)$
and suppose we have
$$
s_i|_{U_{ijk}} = s_{i'}|_{U_{ii'k}}
$$
for all $i, i', k$. Set $t_j = s_{\alpha(j)}|_{V_j}$, where $\mathcal{V}$
and $\alpha$ are as above.

\medskip\noindent
There is one small kink in the argument here. Namely, let
$\mathcal{V}_{jj'} : V_j \cap V_{j'} = \bigcup_{l \in J_{jj'}} V_{jj'l}$
be the covering given to us by the statement of the lemma.
It is not a priori clear that
$$
t_j|_{V_{jj'l}} = t_{j'}|_{V_{jj'l}}
$$
for all $j, j', l$. To see this, note that we do have
$$
t_j|_W = t_{j'}|_W \text{ for all } W \in \mathcal{B},
W \subset V_{jj'l} \cap U_{\alpha(j)\alpha(j')k}
$$
for all $k \in I_{\alpha(j)\alpha(j')}$, by our assumption on
the family of elements $s_i$. And since
$V_j \cap V_{j'} \subset U_{\alpha(j)} \cap U_{\alpha(j')}$
we see that $t_j|_{V_{jj'l}}$ and $t_{j'}|_{V_{jj'l}}$
agree on the members of a covering of $V_{jj'l}$ by
elements of $\mathcal{B}$. Hence by the uniqueness part proved above
we finally deduce the desired equality of
$t_j|_{V_{jj'l}}$ and $t_{j'}|_{V_{jj'l}}$.
Then we get the existence of an element $t \in \mathcal{F}(U)$
by property $(**)$ for $(\mathcal{V}, \mathcal{V}_{jj'})$.

\medskip\noindent
Again there is a small snag. We know that $t$ restricts to $t_j$ on $V_j$
but we do not yet know that $t$ restricts to $s_i$ on $U_i$. To conclude
this note that the sets $U_i \cap V_j$, $j \in J$ cover $U_i$. Hence
also the sets $U_{i \alpha(j) k} \cap V_j$, $j\in J$, $k \in I_{i\alpha(j)}$
cover $U_i$. We leave it to the reader to see that $t$ and $s_i$ restrict
to the same section of $\mathcal{F}$ on any $W \in \mathcal{B}$
which is contained in one of the open sets
$U_{i \alpha(j) k} \cap V_j$, $j\in J$, $k \in I_{i\alpha(j)}$.
Hence by the uniqueness part seen above we win.
\end{proof}
-/

-- Here we will prove that if F is a sheaf-of-types-on-a-basis
