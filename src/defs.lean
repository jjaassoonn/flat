import algebra.category.Module.epi_mono
import linear_algebra.tensor_product
import algebra.module.injective

import .character
import .adjunction_general

universes u v

open_locale tensor_product
open category_theory character_module

namespace Module

variables (R : Type u) [comm_ring R] 
variables (M : Type (max u v)) [add_comm_group M] [module R M]

instance aux1 : module R (R →ₗ[R] M) := linear_map.module
instance aux2 (I : ideal R) : module R (I →ₗ[R] M) := linear_map.module

open_locale big_operators 

@[simps apply]
def restrict_to_ideal (I : ideal R) :
  (R →ₗ[R] M) →ₗ[R] (I →ₗ[R] M) :=
{ to_fun := λ f, f.dom_restrict I,
  map_add' := λ f g, linear_map.ext $ λ x, rfl,
  map_smul' := λ r f, linear_map.ext $ λ x, rfl }

/-
If `I ⊗ M → R ⊗ M` is injective for all ideal `I`, 
then `character_module (R ⊗ M) → character_module (I ⊗ M)` is surjective for 
      ` = R ⊗ M → ℚ/ℤ`            `= I ⊗ M → ℚ/ℤ`
all `I`,
by tensor hom adjunction,
`Hom(R, character_module M) → Hom(I, character_module M)` is surjective for all `I`
so `character_module M` is injective, hence `M` is flat.
-/

instance aux3 (I : ideal R) : module R (I ⊗[R] M) := tensor_product.left_module
instance aux4 : module R (R ⊗[R] M) := tensor_product.left_module

section

variables {R}

@[reducible]
def tensor_embedding (I : ideal R) : (ulift.{max u v} I ⊗[R] M) →ₗ[R] (ulift.{max v u} R ⊗[R] M) :=
tensor_product.map 
{ to_fun := λ i, ulift.up (i.down : R),
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl } 
{ to_fun := id,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl }

end

end Module