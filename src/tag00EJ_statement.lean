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

import Kenny_comm_alg.Zariski localization --tactic.find
universe u

-- I used a list L for [f_1,f_2,...,f_n] (I used [f_0,f_1,...,f_{n-1}] of)
-- I needed to think of it as a set when claiming it generated R
-- and I needed to define a function f : fin n -> R sending i to f_i.
def localise_more_left {R : Type u} [comm_ring R] (f g) : 
  localization.loc R (powers f) → localization.loc R (powers (f * g)) 
  := sorry -- the canonical map

def localise_more_right {R : Type u} [comm_ring R] (f g) :
  localization.loc R (powers g) → localization.loc R (powers (f * g))
  := sorry -- the canonical map;  induce from the previous def?

lemma lemma_standard_covering {R : Type} [comm_ring R] (L : list R) 
(H : (1:R) ∈ generate {x : R | x ∈ L}) :
  let n := list.length L in 
  let f := λ i : fin n, list.nth_le L i.val i.is_lt in
  let α : R → Π (i : fin n), localization.loc R (powers (f i)) 
        := λ r i, localization.of_comm_ring R _ r in
  let β : (Π (i : fin n), localization.loc R (powers (f i))) → 
            Π (j : fin n), Π (k : fin n), localization.loc R (powers (f j * f k)) 
        := λ r, λ j k, localise_more_left (f j) (f k) (r j) - localise_more_right (f j) (f k) (r k) in
  function.injective α ∧ -- image of α is kernel of β (as maps of abelian groups or R-mods)
    ∀ s : (Π (i : fin n), localization.loc R (powers (f i))), ∀ j k, β s j k = 0 ↔ ∃ r : R, α r = s :=
    sorry 
