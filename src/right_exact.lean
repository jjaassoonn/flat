import linear_algebra.tensor_product
import algebra.category.Module.abelian
import algebra.homology.exact

import .adjunction_general

universe u

open category_theory
open_locale tensor_product zero_object

namespace tensor_product

variables (R : Type u) [comm_ring R]
variables (M : Type u) [add_comm_group M] [module R M]
variables (A B C : Module.{u} R)

variables (fAB : A ⟶ B) (fBC : B ⟶ C)
variables [e0A : exact (0 : (0 : Module.{u} R) ⟶ _) fAB] 
variables [eAB : exact fAB fBC] [eC0 : exact fBC (0 : _ ⟶ (0 : Module.{u} R))]

include fAB fBC e0A eAB eC0

/--
```
0 -----> A ---fAB---> B ---fBC---> C ----> 0
``` 
is exact
then
```
A ⊗ M --> B ⊗ M ---> C ⊗ M ----> 0
```
is exact
-/

lemma right_exact.at3 :
  exact 
    (by exact map fBC linear_map.id : Module.of R (B ⊗[R] M) ⟶ Module.of R (C ⊗[R] M))
    (0 : _ ⟶ (0 : Module.{u} R)) :=
begin 
  rw ←epi_iff_exact_zero_right,
  haveI : bimodule R R M,
  { refine ⟨λ r r' m, _⟩,
    rw [←mul_smul, mul_comm, mul_smul] },
  haveI : epi fBC,
  { rw ←epi_iff_exact_zero_right at eC0,
    exact eC0 },
  haveI epi0 : epi ((Module.tensor_functor R R M).map fBC),
  { apply_instance },
  rw Module.epi_iff_surjective at epi0 ⊢,
  exact epi0,
end 

lemma right_exact :
  exact 
    (by exact map fAB linear_map.id : Module.of R (A ⊗[R] M) ⟶ Module.of R (B ⊗[R] M)) 
    (by exact map fBC linear_map.id : Module.of R (B ⊗[R] M) ⟶ Module.of R (C ⊗[R] M)) ∧
  exact 
    (by exact map fBC linear_map.id : Module.of R (B ⊗[R] M) ⟶ Module.of R (C ⊗[R] M))
    (0 : _ ⟶ (0 : Module.{u} R)) :=
⟨sorry, by exactI @@right_exact.at3 R _ M _ _ A B C fAB fBC e0A eAB eC0⟩

end tensor_product