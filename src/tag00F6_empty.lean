/-
Lemma 10.28.1. Let U⊂Spec(R) be open. The following are equivalent:

    U is retrocompact in Spec(R),
    U is quasi-compact,
    U is a finite union of standard opens, and
    there exists a finitely generated ideal I⊂R such that X∖V(I)=U. 

Proof. We have (1) ⇒ (2) because Spec(R) is quasi-compact, see Lemma 10.16.10 (=tag 00E8) . We have (2) ⇒ (3) because standard opens form a basis for the topology. Proof of (3) ⇒ (1). Let U=⋃i=1…nD(fi). To show that U is retrocompact in Spec(R) it suffices to show that U∩V is quasi-compact for any quasi-compact open V of Spec(R). Write V=⋃j=1…mD(gj) which is possible by (2) ⇒ (3). Each standard open is homeomorphic to the spectrum of a ring and hence quasi-compact, see Lemmas 10.16.6 (00E4) and 10.16.10 (00E8). Thus U∩V=(⋃i=1…nD(fi))∩(⋃j=1…mD(gj))=⋃i,jD(figj) is a finite union of quasi-compact opens hence quasi-compact. To finish the proof note that (4) is equivalent to (3) by Lemma 10.16.2 (00E0). 
-/
