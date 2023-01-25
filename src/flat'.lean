import algebra.category.Module.epi_mono
import linear_algebra.tensor_product
import algebra.module.injective

import .character
import .adjunction_general

universes u

open_locale tensor_product
open category_theory character_module

namespace Module

variables (R : Type u) [comm_ring R] 
variables (M : Type u) [add_comm_group M] [module R M]

/--
A module `M` is flat iff for any injective linear map `L : N ⟶ N'`, the induced
map `N ⊗ M ⟶ N' ⊗ M` is also injective
-/
def flat' : Prop := ∀ ⦃N N' : Module.{u} R⦄ (L : N ⟶ N'), 
  function.injective L →
  function.injective (tensor_product.map L (linear_map.id : M →ₗ[R] M)) 

 open_locale big_operators 
/--
Theorem due to J.Lambek, see ![this document](../doc/Lambek.pdf)
-/
lemma Lambek : injective (Module.of R $ character_module M) → flat' R M := 
begin 
  intros h_injective A B L hL,
  haveI : mono L := by rwa concrete_category.mono_iff_injective_of_preserves_pullback,
  rw ←linear_map.ker_eq_bot at ⊢,
  rw eq_bot_iff at ⊢,
  rintros z hz,
  rw submodule.mem_bot,
  rw linear_map.mem_ker at hz,
  by_cases rid : z = 0, 
  { exact rid },
  exfalso,
  obtain ⟨g, hg⟩ := character_module.non_zero.{u} (A ⊗[R] M) rid,
  work_on_goal 2 { exact R },
  work_on_goal 2 { apply_instance },
  work_on_goal 2 { exact tensor_product.left_module },
  set f : A →ₗ[R] (character_module M) := 
  { to_fun := λ a, { to_fun := λ m, g (a ⊗ₜ m), map_add' := _, map_smul' := _ }, 
    map_add' := _, map_smul' := _ } with f_eq,
  work_on_goal 2 { intros m m', rw [tensor_product.tmul_add, map_add], },
  work_on_goal 2 { intros zz m, rw [ring_hom.id_apply, ←tensor_product.smul_tmul, 
    ←tensor_product.smul_tmul', map_zsmul], },
  work_on_goal 2 { intros a a', ext1 t, simp only [linear_map.coe_mk, linear_map.add_apply, 
    tensor_product.add_tmul, map_add], },
  work_on_goal 2 { intros r a, ext1 t, simp only [linear_map.coe_mk, linear_map.smul_apply, 
    character_module.smul_apply, ring_hom.id_apply, tensor_product.smul_tmul], },
  obtain ⟨f' : B →ₗ[R] (character_module M), hf'⟩ := h_injective.factors f L,
  set g' : (character_module $ B ⊗[R] M) := character_module.hom_equiv _ _ f' with g'_eq,
  obtain ⟨ι, a, m, s, rfl⟩ := tensor_product.exists_rep _ z,
  have EQ : g' (∑ i in s, L (a i) ⊗ₜ m i) = 0,
  { simp_rw [map_sum, tensor_product.map_tmul, linear_map.id_apply] at hz,
    rw hz, rw map_zero, },
  refine hg _,
  rw map_sum,
  simp_rw [map_sum, g'_eq, hom_equiv_apply, add_monoid_hom.coe_to_int_linear_map,
      tensor_product.to_add_comm_group'.apply_tmul] at EQ,
  convert EQ using 1,
  refine finset.sum_congr rfl (λ i hi, _),
  erw fun_like.congr_fun hf',
  rw f_eq,
  refl,
end

lemma flat'_of_baer : module.Baer.{u u} R (character_module.{u} M) → flat' R M := 
λ h, Lambek _ _ $ (module.injective_iff_injective_object.{u u} R 
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

@[reducible]
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

lemma injective_character (hIs : ∀ (I : ideal R), function.injective (tensor_embedding M I)) : 
  module.Baer.{u u} R (character_module M) :=
begin 
  rw module.Baer_iff,
  intros I l,
  obtain ⟨F, hF⟩ := surj1 _ _ (hIs I) (character_module.hom_equiv _ _ l),
  refine ⟨(character_module.hom_equiv _ _).symm F, _⟩,
  ext i m : 2,
  rw restrict_to_ideal_apply,
  rw linear_map.dom_restrict_apply,
  rw character_module.hom_equiv,
  rw equiv.coe_fn_symm_mk,
  rw linear_map.coe_mk,
  rw linear_map.coe_mk,
  have EQ := fun_like.congr_fun hF (i ⊗ₜ m),
  rw character_module.map_apply at EQ,
  rw linear_map.coe_mk at EQ,
  rw tensor_product.map_tmul at EQ,
  rw linear_map.coe_mk at EQ,
  rw linear_map.coe_mk at EQ,
  rw id at EQ,
  rw EQ,
  rw character_module.hom_equiv_apply,
  rw add_monoid_hom.coe_to_int_linear_map,
  rw tensor_product.to_add_comm_group'.apply_tmul,
end

/--
`tensor_embedding M I` is the canonical map `I ⊗ M ⟶ R ⊗ M`
-/
lemma flat'_of_ideal (hIs : ∀ (I : ideal R), function.injective (tensor_embedding M I)) :
  flat' R M :=
begin 
  apply flat'_of_baer,
  apply injective_character,
  assumption,
end

end content

end Module