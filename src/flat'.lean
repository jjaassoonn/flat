import algebra.category.Module.epi_mono
import linear_algebra.tensor_product
import algebra.module.injective

import .character

universes u

open_locale tensor_product
open category_theory

namespace Module

variables (R : Type u) [comm_ring R] 
variables (M : Type u) [add_comm_group M] [module R M]

/--
A module `M` is flat iff for any injective linear map `L : N ⟶ N'`, the induced
map `N ⊗ M ⟶ N' ⊗ M` is also injective
-/
def flat' : Prop := ∀ ⦃N N' : Module R⦄ (L : N ⟶ N'), 
  function.injective L →
  function.injective (tensor_product.map L (linear_map.id : M →ₗ[R] M)) 
  
/--
Theorem due to J.Lambek, see ![this document](../doc/Lambek.pdf)
-/
lemma Lambek : flat' R M ↔ injective (Module.of R $ character_module M) := sorry

lemma flat'_of_baer : module.Baer.{u u} R (character_module.{u} M) → flat' R M := 
  λ h, (Lambek _ _).mpr $ (module.injective_iff_injective_object.{u u} R 
      (character_module M)).mp (module.Baer.injective h)

@[simps apply]
def restrict_to_ideal (I : ideal R) :
  (R →ₗ[R] M) →ₗ[R] (I →ₗ[R] M) :=
{ to_fun := λ f, f.dom_restrict I,
  map_add' := λ f g, linear_map.ext $ λ x, rfl,
  map_smul' := λ r f, linear_map.ext $ λ x, rfl }

-- need tensor hom adjunction
-- lemma restrict_to_ideal_character_module (I : ideal R) :
--   restrict_to_ideal R (character_module M) I = _

lemma module.Baer_iff : 
  module.Baer.{u u} R M ↔ 
  ∀ I, function.surjective (restrict_to_ideal R M I) :=
begin 
  split,
  { intros h I g,
    obtain ⟨g', hg'⟩ := h I g,
    refine ⟨g', _⟩,
    rw restrict_to_ideal_apply,
    ext1,
    rw linear_map.dom_restrict_apply, 
    rw hg' x x.2, congr, ext, refl,  },
  { intros h I g,
    obtain ⟨g', hg'⟩ := h I g,
    refine ⟨g', λ x hx, _⟩,
    rw ←hg',
    rw restrict_to_ideal_apply,
    rw linear_map.dom_restrict_apply,
    congr, },
end

lemma flat'_of_surj : 
  (∀ I, function.surjective (restrict_to_ideal R (character_module M) I)) → flat' R M := 
λ h, flat'_of_baer _ _ ((module.Baer_iff _ _).mpr h)

/-
If `I ⊗ M → R ⊗ M` is injective for all ideal `I`, 
then `character_module (R ⊗ M) → character_module (I ⊗ M)` is surjective for 
      ` = R ⊗ M → ℚ/ℤ`            `= I ⊗ M → ℚ/ℤ`
all `I`,
by tensor hom adjunction,
`Hom(R, character_module M) → Hom(I, character_module M)` is surjective for all `I`
so `character_module M` is injective, hence `M` is flat.
-/

end Module