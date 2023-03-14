import category_theory.functor.left_derived
import category_theory.monoidal.tor
import category_theory.monoidal.braided

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory

section

variables {C : Type u} [category.{v} C] {D : Type*} [category D]

-- Importing `category_theory.abelian.projective` and assuming
-- `[abelian C] [enough_projectives C] [abelian D]` suffices to acquire all the following:
variables [preadditive C] [has_zero_object C] [has_equalizers C]
  [has_images C] [has_projective_resolutions C]
variables [preadditive D] [has_equalizers D] [has_cokernels D]
  [has_images D] [has_image_maps D]

@[simps]
def nat_iso.left_derived {F G : C ⥤ D} [F.additive] [G.additive] (α : F ≅ G) (n : ℕ) :
  F.left_derived n ≅ G.left_derived n :=
{ hom := α.hom.left_derived n,
  inv := α.inv.left_derived n,
  hom_inv_id' := by rw [←nat_trans.left_derived_comp, iso.hom_inv_id, nat_trans.left_derived_id],
  inv_hom_id' := by rw [←nat_trans.left_derived_comp, iso.inv_hom_id, nat_trans.left_derived_id], }

end

section

variables {C : Type*} [category C] 
  [monoidal_category C] [symmetric_category C] [preadditive C] 
  [monoidal_preadditive C]
  [has_zero_object C] [has_equalizers C] [has_cokernels C] [has_images C] [has_image_maps C]
  [has_projective_resolutions C]

/--

`(Tor C n).obj X` is left deriving the functor `X ⊗ -`, i.e. `((Tor C n).obj X).obj Y` is
- take a projective resolution of `P_* → Y` and apply `X ⊗ -` to yield
```
X ⊗ P_n → X ⊗ P_{n-1} → ⋯
```
and calculate homology
-/
def Tor.is_balanced (n : ℕ) (X Y) : ((Tor C n).obj X).obj Y ⟶ ((Tor' C n).obj Y).obj X :=
show ((monoidal_category.tensor_left X).left_derived n).obj Y ⟶ 
  ((monoidal_category.tensor_right X).left_derived n).obj Y,
from 
(nat_trans.left_derived 
({ app := λ Y, (β_ X Y).hom,
  naturality' := λ Y Y' f, by simp } : 
  monoidal_category.tensor_left X ⟶ monoidal_category.tensor_right X) n).app Y

#check nat_iso.hom_app_is_iso

end

end category_theory