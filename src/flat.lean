import algebra.homology.exact
import algebra.category.Module.abelian
import category_theory.limits.shapes.images

import .defs
import .ideal_and_fg_ideal
import .right_exact
import .ses


open category_theory category_theory.limits category_theory.monoidal_category  
open Module character_module
open_locale tensor_product zero_object big_operators

universe u

namespace module

variables (R : Type u) [comm_ring R] 
variables (M : Type u) [add_comm_group M] [module R M]

namespace flat

section defs

/--
0 ---> N₁ ----> N₂ ----> N₃ ----> 0
-/
@[reducible]
protected def ses : Prop :=
(tensor_right (Module.of R M)).is_exact

/--
    l12      l23
N1 ----> N2 -----> N3 is exact

we have 0 ---> ker l23 ---> N2 ---> coker l23 ---> 0 exact

ker l23 ⊗ M ⟶ N2 ⊗ M is injective

Want to show
        l12 ⊗ 1      l23 ⊗ 1
N1 ⊗ M --------> N2 --------> N3

-/
protected def exact : Prop :=
∀ ⦃N1 N2 N3 : Module.{u} R⦄ (l12 : N1 ⟶ N2) (l23 : N2 ⟶ N3)
  (he : exact l12 l23),
  exact ((tensor_right $ Module.of R M).map l12)
    ((tensor_right $ Module.of R M).map l23)

protected def inj : Prop :=
∀ ⦃N N' : Module.{u} R⦄ (L : N ⟶ N'), 
  function.injective L →
  function.injective ((tensor_right (Module.of R M)).map L) 

protected def ideal : Prop :=
∀ (I : ideal R), function.injective (tensor_embedding M I)

protected def fg_ideal : Prop :=
∀ (I : ideal R), I.fg → function.injective (tensor_embedding M I)

end defs

section ses_iff_inj

lemma ses_of_inj (H : module.flat.inj R M) :  module.flat.ses R M := -- λ N1 N2 N3 l12 l23 he1 he2 he3,
{ map_exact := 
  begin 
    rintros ⟨N1, N2, N3, l12, l23⟩ ⟨he1, he2, he3⟩,
    dsimp only at *,
    have inj1 : function.injective (tensor_product.map l12 linear_map.id),
    { rw ←mono_iff_exact_zero_left at he1,
      rw concrete_category.mono_iff_injective_of_preserves_pullback at he1,
      exact H l12 he1, },
  
    obtain ⟨e1, e2⟩ := @@tensor_product.right_exact R _ M _ _ N1 N2 N3 l12 l23 he2 he3,
    refine ⟨_, e1, e2⟩,
    { rw ←mono_iff_exact_zero_left,
      rwa concrete_category.mono_iff_injective_of_preserves_pullback, },
  end }

lemma inj_of_ses (H : module.flat.ses R M) : module.flat.inj R M := λ N1 N2 l hl, 
begin 
  resetI,
  obtain ⟨e1, e2, e3⟩ := @@functor.is_exact.map_exact _ _ _ _ H ⟨_, _, _, l, (cokernel.π l)⟩ ⟨_, _, _⟩,
  { rwa [←mono_iff_exact_zero_left, Module.mono_iff_injective] at e1, },
  { rwa [←mono_iff_exact_zero_left, Module.mono_iff_injective], },
  { exact abelian.exact_cokernel l, },
  exact @@exact_epi_zero _ _ _ _ _ _ _,
end

end ses_iff_inj

lemma ideal_of_fg_ideal (H : module.flat.fg_ideal R M) : module.flat.ideal R M :=
λ I, by classical; exact tensor_embedding_inj_of_fg_inj M I H

section inj_of_ideal

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

lemma Lambek : category_theory.injective (Module.of R $ character_module M) → module.flat.inj R M := 
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
  obtain ⟨g, hg⟩ := character_module.non_zero (A ⊗[R] M) rid,
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
  { simp only [tensor_right_map, linear_map.map_sum, monoidal_category.hom_apply, 
      Module.id_apply] at hz,
    rw [hz, map_zero], },
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

lemma flat'_of_baer : module.Baer.{u u} R (character_module M) → module.flat.inj R M := 
λ h, Lambek _ _ $ (module.injective_iff_injective_object.{u u} R 
    (character_module M)).mp (module.Baer.injective h)

lemma flat'_of_surj : 
  (∀ I, function.surjective (restrict_to_ideal R (character_module M) I)) → module.flat.inj R M := 
λ h, flat'_of_baer _ _ ((module.Baer_iff _ _).mpr h)


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
  simp only [restrict_to_ideal_apply, linear_map.dom_restrict_apply, character_module.hom_equiv, 
    equiv.coe_fn_symm_mk, linear_map.coe_mk],
  have EQ := fun_like.congr_fun hF (i ⊗ₜ m),
  simpa only [character_module.hom_equiv_apply, add_monoid_hom.coe_to_int_linear_map, 
    tensor_product.to_add_comm_group'.apply_tmul] using EQ,
end

/--
`tensor_embedding M I` is the canonical map `I ⊗ M ⟶ R ⊗ M`
-/
lemma inj_of_ideal (hIs : module.flat.ideal R M) :
  module.flat.inj R M :=
begin 
  apply flat'_of_baer,
  apply injective_character,
  assumption
end

end inj_of_ideal

lemma fg_ideal_of_inj (H : module.flat.inj R M) : module.flat.fg_ideal R M :=
begin 
  intros I hI,
  refine @H ⟨I⟩ ⟨R⟩ ⟨coe, λ _ _, rfl, λ _ _, rfl⟩ _,
  intros z z' h,
  ext1,
  simpa only [linear_map.coe_mk] using h,
end

lemma exact_of_ses (H : module.flat.ses R M) :
  module.flat.exact R M :=
λ N1 N2 N3 l12 l23 he, functor.map_exact _ _ _ he

lemma inj_of_exact (H : module.flat.exact R M) :
  module.flat.inj R M :=
λ N1 N2 l h,
begin 
  have e0 : exact (0 : (0 : Module.{u} R) ⟶ _) l,
  { rw ←Module.mono_iff_injective at h,
    resetI,
    apply exact_zero_left_of_mono, },
  specialize H (0 : (0 : Module.{u} R) ⟶ N1) l e0,
  have eq1 : ((tensor_right (Module.of R M)).map 0) = 
    (_ : Module.of R ((0 : Module.{u} R) ⊗ M) ⟶ 0) ≫ (0 : (0 : Module.{u} R) ⟶ Module.of R (N1 ⊗ M)),
  work_on_goal 3 
  { refine tensor_product.lift 0, },
  { refine linear_map.ext (λ z, z.induction_on _ (λ z m, _) (λ x y hx hy, _)), 
    { simp only [map_zero] },
    { simp only [tensor_right_map, monoidal_preadditive.zero_tensor, comp_zero], },
    { rw [map_add, hx, hy, map_add], }, },
  rw eq1 at H,
  rw abelian.exact_epi_comp_iff at H,
  rw ←mono_iff_exact_zero_left at H,
  rwa Module.mono_iff_injective at H,
end

lemma equiv_defs : tfae 
  [module.flat.ses R M
  , module.flat.inj R M
  , module.flat.ideal R M
  , module.flat.fg_ideal R M
  , module.flat.exact R M] :=
begin 
  tfae_have : 1 → 2, { apply inj_of_ses },
  tfae_have : 2 → 1, { apply ses_of_inj },
  tfae_have : 3 → 2, { apply inj_of_ideal },
  tfae_have : 4 → 3, { apply ideal_of_fg_ideal },
  tfae_have : 2 → 4, { apply fg_ideal_of_inj },
  tfae_have : 5 → 2, { apply inj_of_exact },
  tfae_have : 1 → 5, { apply exact_of_ses },
  tfae_finish,
end

end flat

end module
