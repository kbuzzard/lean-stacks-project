import analysis.topology.topological_space
import tag006E -- presheaves 

definition stalk {X : Type*} [TX : topological_space X] (FPT : presheaf_of_types X) (x : X) :=
sorry
-- 
-- set Z is pairs (U,s) with U an open in X and x in U and s in FPT.F(U)
-- equiv reln on Z : (U,s) tilde (V,t) iff there exists W open 
-- such that x in W, W in U, W in V, and FPT.res (U to W) s = FPT.res (V to W) t
