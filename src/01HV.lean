/-
Lemma 25.5.4. Let R be a ring. Let M be an R-module. Let M˜ be the sheaf of Spec(R)-modules associated to M.

    We have Γ(Spec(R),Spec(R))=R.
    We have Γ(Spec(R),M˜)=M as an R-module.
    For every f∈R we have Γ(D(f),Spec(R))=Rf.
    For every f∈R we have Γ(D(f),M˜)=Mf as an Rf-module.
    Whenever D(g)⊂D(f) the restriction mappings on Spec(R) and M˜ are the maps Rf→Rg and Mf→Mg from Lemma 25.5.1 (01HS)
    Let 𝔭 be a prime of R, and let x∈Spec(R) be the corresponding point. We have Spec(R),x=R𝔭.
    Let 𝔭 be a prime of R, and let x∈Spec(R) be the corresponding point. We have x=M𝔭 as an R𝔭-module. 

Moreover, all these identifications are functorial in the R module M. In particular, the functor M↦M˜ is an exact functor from the category of R-modules to the category of Spec(R)-modules.

Proof. Assertions (1) - (7) are clear from the discussion above. The exactness of the functor M↦M˜ follows from the fact that the functor M↦M𝔭 is exact and the fact that exactness of short exact sequences may be checked on stalks, see Modules, Lemma 17.3.1 (01AG). 
-/
