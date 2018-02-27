/-
Definition 25.5.3. Let R be a ring.

    The structure sheaf Spec(R) of the spectrum of R is the unique sheaf of rings Spec(R) which agrees with R˜ on the basis of standard opens.
    The locally ringed space (Spec(R),Spec(R)) is called the spectrum of R and denoted Spec(R).
    The sheaf of Spec(R)-modules extending M˜ to all opens of Spec(R) is called the sheaf of Spec(R)-modules associated to M. This sheaf is denoted M˜ as well. 
-/

/- NB this mostly follows from the discussion in 01HR after 25.5.2 and before 25.5.3. I will quote it here.

 Let R be a ring. Let M be an R-module. We will define a presheaf M˜ on the basis of standard opens. Suppose that U⊂Spec(R) is a standard open. If f,g∈R are such that D(f)=D(g), then by Lemma 25.5.1 above there are canonical maps Mf→Mg and Mg→Mf which are mutually inverse. Hence we may choose any f such that U=D(f) and define
M˜(U)=Mf.
Note that if D(g)⊂D(f), then by Lemma 25.5.1 above we have a canonical map
M˜(D(f))=Mf⟶Mg=M˜(D(g)).
Clearly, this defines a presheaf of abelian groups on the basis of standard opens. If M=R, then R˜ is a presheaf of rings on the basis of standard opens.

Let us compute the stalk of M˜ at a point x∈Spec(R). Suppose that x corresponds to the prime 𝔭⊂R. By definition of the stalk we see that
M˜x=colimf∈R,f∉𝔭Mf
Here the set {f∈R,f∉𝔭} is preordered by the rule f≥f′⇔D(f)⊂D(f′). If f1,f2∈R∖𝔭, then we have f1f2≥f1 in this ordering. Hence by Algebra, Lemma 10.9.9 we conclude that
M˜x=M𝔭.

Next, we check the sheaf condition for the standard open coverings. If D(f)=⋃ni=1D(gi), then the sheaf condition for this covering is equivalent with the exactness of the sequence
0→Mf→⨁Mgi→⨁Mgigj.
Note that D(gi)=D(fgi), and hence we can rewrite this sequence as the sequence
0→Mf→⨁Mfgi→⨁Mfgigj.
In addition, by Lemma 25.5.1 (01HS)  above we see that g1,…,gn generate the unit ideal in Rf. Thus we may apply Algebra, Lemma 10.22.2 (00EK) to the module Mf over Rf and the elements g1,…,gn. We conclude that the sequence is exact. By the remarks made above, we see that M˜ is a sheaf on the basis of standard opens.

Thus we conclude from the material in Sheaves, Section 6.30 (009H) that there exists a unique sheaf of rings Spec(R) which agrees with R˜ on the standard opens. Note that by our computation of stalks above, the stalks of this sheaf of rings are all local rings.

Similarly, for any R-module M there exists a unique sheaf of Spec(R)-modules  which agrees with M˜ on the standard opens, see Sheaves, Lemma 6.30.12. (009T)

-/
