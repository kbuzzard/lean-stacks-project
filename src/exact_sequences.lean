import Kenny_comm_alg.temp linear_algebra.linear_map_module

universes u v w

variables {R : Type u} [ring R]

namespace linear_map

variables {M : Type v} {N : Type w}
variables [module R M] [module R N]
variables (f : linear_map M N)

def coim := is_submodule.quotient M (ker f)

instance coim.module : module R (coim f) :=
is_submodule.quotient.module _

def coim.to_im : coim f → N :=
is_submodule.quotient.lift _ f.2 (λ x, id)

end linear_map

variables (obj : ℤ → Type v)
variables (Hobj : ∀ n, module R $ obj n)
variables (mor : ∀ n, linear_map (obj (n+1)) (obj n))

instance module.to_has_zero (M : Type v) [module R M] : has_zero M :=
by apply_instance

include obj Hobj mor

class is_complex : Prop :=
(im_sub_ker : ∀ n x, mor n ((mor (n+1)).1 x) = @has_zero.zero _ (@module.to_has_zero R _ _ (Hobj n)))

class is_exact extends is_complex obj Hobj mor :=
(ker_to_coim : ∀ n, linear_map (linear_map.ker (mor n)) (linear_map.coim (mor (n + 1))))
(right_inv : ∀ n x, linear_map.coim.to_im _ (ker_to_coim n x) = x)
(left_inv : ∀ n x, ker_to_coim n ⟨linear_map.coim.to_im (mor (n + 1)) x,
   begin
     apply @quotient.induction_on _ (is_submodule.quotient_rel _) _ x,
     intro z,
     dsimp [linear_map.coim.to_im, linear_map.ker],
     exact is_complex.im_sub_ker _ _ _
   end⟩ = x)

-- is there a better way of doing it?