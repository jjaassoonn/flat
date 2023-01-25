import algebra.category.Module.epi_mono
import linear_algebra.tensor_product
import algebra.module.injective

import .character
import .adjunction_general

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

instance aux1 : module R (R →ₗ[R] M) := linear_map.module
instance aux2 (I : ideal R) : module R (I →ₗ[R] M) := linear_map.module

@[simps apply]
def restrict_to_ideal (I : ideal R) :
  (R →ₗ[R] M) →ₗ[R] (I →ₗ[R] M) :=
{ to_fun := λ f, f.dom_restrict I,
  map_add' := λ f g, linear_map.ext $ λ x, rfl,
  map_smul' := λ r f, linear_map.ext $ λ x, rfl }

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

instance aux3 (I : ideal R) : module R (I ⊗[R] M) := tensor_product.left_module
instance aux4 : module R (R ⊗[R] M) := tensor_product.left_module

section

variables {R}

@[simps]
def tensor_embedding (I : ideal R) : (I ⊗[R] M) →ₗ[R] (R ⊗[R] M) :=
tensor_product.map 
{ to_fun := coe,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl } 
{ to_fun := id,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl }

end

namespace content

variables {I : ideal R} (hI : function.injective (tensor_embedding M I))

lemma surj1 : function.surjective (character_module.map (tensor_embedding M I)) :=
character_module.map_inj _ hI

@[simps]
def character_module_map' : (character_module (R ⊗[R] M)) →ₗ[R] (character_module (I ⊗[R] M)) :=
{ to_fun := λ l, 
  { to_fun := λ x, l (tensor_embedding _ I x),
    map_zero' := by rw [map_zero, map_zero],
    map_add' := λ z z', by rw [map_add, map_add] },
  map_add' := λ f g, add_monoid_hom.ext $ λ z, by simp only [add_monoid_hom.coe_mk,
    add_monoid_hom.add_apply],
  map_smul' := λ r f, add_monoid_hom.ext $ λ z, by { simp only [add_monoid_hom.coe_mk, 
    ring_hom.id_apply, character_module.smul_apply, (tensor_embedding M I).map_smul r z], } }

lemma character_module.map_tensor_embedding :
  character_module.map (tensor_embedding M I) = 
  character_module_map' R M :=
linear_map.ext $ λ l, add_monoid_hom.ext $ λ z',
begin 
  rw character_module_map'_apply_apply,
  rw character_module.map_apply,
  rw add_monoid_hom.comp_apply,
  refl,
end

lemma injective_character : module.Baer.{u u} R (character_module M) :=
begin 
  rw module.Baer_iff,
  intros I l,
  refine ⟨_, _⟩,
  { have := @Module.tensor_hom_adjunction R ℤ _ _ M _ _ _ (bimodule.int _),
    have : R →ₗ[R] (character_module M) := (this.hom_equiv (Module.of R R) (Module.of _ rat_circle) _) _,
      },
end

example : (R →ₗ[R] character_module M) →ₗ[R] (I →ₗ[R] character_module M) :=
{ to_fun := λ l, l.comp $ show I →ₗ[R] R, from 
    { to_fun := coe, map_add' := λ _ _, rfl, map_smul' := λ _ _, rfl },
  map_add' := λ l l', by rw [linear_map.add_comp],
  map_smul' := λ r l, by rw [linear_map.smul_comp, ring_hom.id_apply] }


end content

end Module