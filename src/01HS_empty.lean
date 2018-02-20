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

Proof. Recall that D(g)=Spec(Rg) (see tag 00E4). Thus (a) holds because f maps to an element of Rg which is not contained in any prime ideal, and hence invertible, see tag 00E0. Write the inverse of f in Rg as a/gd. This means gd−af is annihilated by a power of g, whence (b). For (c), the map Rf→Rg exists by (a) from the universal property of localization, or we can define it by mapping b/fn to anb/gne. The equality Mf=M⊗RRf can be used to obtain the map on modules, or we can define Mf→Mg by mapping x/fn to anx/gne.

Recall that D(f) is quasi-compact, see tag 00F6. Hence the second statement follows directly from the fact that the standard opens form a basis for the topology.

The third statement follows directly from tag 00E0. 
-/
