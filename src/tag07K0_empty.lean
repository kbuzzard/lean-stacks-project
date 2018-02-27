/-
Lemma 10.9.7. Let R be a ring. Let S⊂R a multiplicative subset. Let M, N be R-modules. Assume all the elements of S act as automorphisms on N. Then the canonical map
HomR(S−1M,N)⟶HomR(M,N)
induced by the localization map, is an isomorphism.

Proof. It is clear that the map is well-defined and R-linear. Injectivity: Let α∈HomR(S−1M,N) and take an arbitrary element m/s∈S−1M. Then, since s⋅α(m/s)=α(m/1), we have α(m/s)=s−1(α(m/1)), so α is completely determined by what it does on the image of M in S−1M. Surjectivity: Let β:M→N be a given R-linear map. We need to show that it can be "extended" to S−1M. Define a map of sets
M×S→N,(m,s)↦s−1β(m)
Clearly, this map respects the equivalence relation from above, so it descends to a well-defined map α:S−1M→N. It remains to show that this map is R-linear, so take r,r′∈R as well as s,s′∈S and m,m′∈M. Then
α(r⋅m/s+r′⋅m′/s′)=α((r⋅s′⋅m+r′⋅s⋅m′)/(ss′))=(ss′)−1(β(r⋅s′⋅m+r′⋅s⋅m′)=(ss′)−1(r⋅s′β(m)+r′⋅sβ(m′)=rα(m/s)+r′α(m′/s′)
and we win. 
-/

