import algebra.module.localized_module
import ring_theory.localization.at_prime

variables (R : Type*) [comm_ring R] (p : ideal R) [ideal.is_prime p]
variables (M N : Type*) [add_comm_group M] [add_comm_group N] [module R M] [module R N]
variables (l : M →ₗ[R] N)

namespace localized_module

noncomputable def map : localized_module (ideal.prime_compl p) M →ₗ[R] localized_module (ideal.prime_compl p) N :=
localized_module.lift _ ((localized_module.mk_linear_map _ _).comp l) $ λ x, 
begin
  rw module.End_is_unit_iff,
  split,
  { rintros z1 z2 (h : _ • z1 = _ • z2),
    sorry },
  { rintros z,
    change ∃ t, _ • t = _,
    sorry }
end

end localized_module