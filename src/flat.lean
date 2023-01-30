import algebra.homology.exact
import algebra.category.Module.abelian
import category_theory.limits.shapes.images

import .ideal_and_fg_ideal
import .flat'
import .right_exact


open category_theory Module
open_locale tensor_product zero_object

universes u

namespace module

variables (R : Type u) [comm_ring R] 
variables (M : Type u) [add_comm_group M] [module R M]

namespace flat

section defs

instance hmmm0 : Π (N : Module.{u} R), module R (N ⊗[R] M) :=
λ _, tensor_product.left_module

/--
0 ---> N₁ ----> N₂ ----> N₃ ----> 0
-/
protected def ses : Prop :=
∀ ⦃N1 N2 N3 : Module.{u u} R⦄ (l12 : N1 ⟶ N2) (l23 : N2 ⟶ N3)
  (he1 : exact (0 : (0 : Module.{u} R) ⟶ N1) l12)
  (he2 : exact l12 l23)
  (he3 : exact l23 (0 : N3 ⟶ (0 : Module.{u} R))),
exact 
  (0 : (0 : Module.{u} R) ⟶ Module.of R (N1 ⊗[R] M))  
  (by exact tensor_product.map l12 linear_map.id : 
    Module.of R (N1 ⊗[R] M) ⟶ Module.of R (N2 ⊗[R] M)) ∧
exact 
  (by exact tensor_product.map l12 linear_map.id : 
    Module.of R (N1 ⊗[R] M) ⟶ Module.of R (N2 ⊗[R] M)) 
  (by exact tensor_product.map l23 linear_map.id : 
    Module.of R (N2 ⊗[R] M) ⟶ Module.of R (N3 ⊗[R] M)) ∧
exact
  (by exact tensor_product.map l23 linear_map.id : 
    Module.of R (N2 ⊗[R] M) ⟶ Module.of R (N3 ⊗[R] M))
  (0 : _ ⟶ 0)

protected def inj : Prop :=
∀ ⦃N N' : Module.{u} R⦄ (L : N ⟶ N'), 
  function.injective L →
  function.injective (tensor_product.map L (linear_map.id : M →ₗ[R] M)) 

protected def of_ideal : Prop :=
∀ (I : ideal R), function.injective (tensor_embedding M I)

protected def of_fg_ideal : Prop :=
∀ (I : ideal R), I.fg → function.injective (tensor_embedding M I)

end defs

namespace ses_iff_inj

lemma ses_of_inj (H : module.flat.inj R M) :  module.flat.ses R M := λ N1 N2 N3 l12 l23 he1 he2 he3,
begin 
  have inj1 : function.injective (tensor_product.map l12 linear_map.id),
  { rw ←mono_iff_exact_zero_left at he1,
    rw concrete_category.mono_iff_injective_of_preserves_pullback at he1,
    exact H l12 he1, },
  
  have res := @@tensor_product.right_exact R _ M _ _ N1 N2 N3 l12 l23 he1 he2 he3,
  refine ⟨_, res⟩,
  { rw ←mono_iff_exact_zero_left,
    rwa concrete_category.mono_iff_injective_of_preserves_pullback, },
end

lemma inj_of_ses (H : module.flat.ses R M) : module.flat.inj R M := λ N1 N2 l hl, 
begin 
  specialize H l (category_theory.limits.cokernel.π l) _ _ _,
  { rw ←mono_iff_exact_zero_left,
    rwa Module.mono_iff_injective, },
  { exact abelian.exact_cokernel l, },
  { exact exact_epi_zero (limits.cokernel.π l), },
  rw ←mono_iff_exact_zero_left at H,
  rw Module.mono_iff_injective at H,
  exact H.1,
end


end ses_iff_inj


end flat


end module