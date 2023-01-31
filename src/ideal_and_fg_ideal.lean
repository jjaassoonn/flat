import algebra.direct_limit
import algebra.category.fgModule.basic

import .defs
import .direct_lim

open_locale tensor_product

universes u v
variables {R : Type u} [comm_ring R]
variables (M : Type u) [add_comm_group M] [module R M]

variable (I : ideal R)

@[ext]
structure fg_subideal :=
(to_ideal : ideal R)
(fg : to_ideal.fg)
(le : to_ideal ≤ I)

instance hmmm0 : Π (i : fg_subideal I), add_comm_group $ i.to_ideal ⊗[R] M :=
λ _, infer_instance

instance hmmm1 : Π (i : fg_subideal I), module R (i.to_ideal ⊗[R] M) :=
λ _, tensor_product.left_module

instance  : preorder (fg_subideal I) :=
preorder.lift fg_subideal.to_ideal

instance : is_directed (fg_subideal I) (≤) :=
{ directed := λ J J', ⟨⟨J.to_ideal ⊔ J'.to_ideal, submodule.fg.sup J.fg J'.fg, 
    sup_le_iff.mpr ⟨J.le, J'.le⟩⟩, 
    ⟨@le_sup_left (ideal R) _ J.to_ideal J'.to_ideal, 
      @le_sup_right (ideal R) _ J.to_ideal J'.to_ideal⟩⟩ }

instance : inhabited (fg_subideal I) :=
⟨⟨⊥, submodule.fg_bot, bot_le⟩⟩

variables {I}
@[simps] def principal_fg_subideal (i : I) : fg_subideal I :=
{ to_ideal := ideal.span {i},
  fg := submodule.fg_span_singleton _,
  le := submodule.span_le.mpr $ λ x hx, (set.mem_singleton_iff.mp hx).symm ▸ i.2 }

lemma principal_fg_subideal_smul (r : R) (i : I) :
  principal_fg_subideal (r • i) ≤ principal_fg_subideal i :=
submodule.span_le.mpr $ λ x hx, (set.mem_singleton_iff.mp hx).symm ▸ 
submodule.mem_span_singleton.mpr ⟨r, rfl⟩

lemma mem_principal_fg_subideal (i : I) : (i : R) ∈ (principal_fg_subideal i).to_ideal :=
submodule.mem_span_singleton_self _

@[simps] def doubleton_fg_subideal (i j : I) : fg_subideal I :=
{ to_ideal := ideal.span {i, j},
  fg := submodule.fg_span $ by simp only [set.finite.insert, set.finite_singleton],
  le := submodule.span_le.mpr $ λ x hx, 
  begin 
    simp only [set.mem_insert_iff, set.mem_singleton_iff] at hx,
    rcases hx with rfl|rfl,
    { exact i.2 },
    { exact j.2 }
  end }

lemma mem_left_doubleton_fg_subideal (i j : I) :
  (i : R) ∈ (doubleton_fg_subideal i j).to_ideal := 
submodule.subset_span $ by simp

lemma mem_right_doubleton_fg_subideal (i j : I) :
  (j : R) ∈ (doubleton_fg_subideal i j).to_ideal := 
submodule.subset_span $ by simp

lemma left_le_doubleton_fg_subideal (i j : I) :
  principal_fg_subideal i ≤ doubleton_fg_subideal i j :=
submodule.span_le.mpr $ λ x hx, (set.mem_singleton_iff.mpr hx).symm ▸ 
  submodule.subset_span (by simp)

lemma right_le_doubleton_fg_subideal (i j : I) :
  principal_fg_subideal j ≤ doubleton_fg_subideal i j :=
submodule.span_le.mpr $ λ x hx, (set.mem_singleton_iff.mpr hx).symm ▸ 
  submodule.subset_span (by simp)

lemma add_le_doubleton_fg_subideal (i j : I) :
  principal_fg_subideal (i + j) ≤ doubleton_fg_subideal i j :=
submodule.span_le.mpr $ λ x hx, 
begin
  rw set.mem_singleton_iff at hx,
  rw hx,
  change (i : R) + (j : R) ∈ _,
  refine (doubleton_fg_subideal i j).to_ideal.add_mem _ _, 
  { apply mem_left_doubleton_fg_subideal, },
  { apply mem_right_doubleton_fg_subideal, },
end

variable (I)

variable [decidable_eq $ fg_subideal I]

namespace ideal

instance : Π (i : fg_subideal I), add_comm_group $ i.to_ideal :=
λ _, infer_instance

@[reducible]
def as_direct_limit :=
module.direct_limit (λ (i : fg_subideal I), i.to_ideal) $ λ i j hij, 
  (submodule.of_le hij : i.to_ideal →ₗ[R] j.to_ideal)

@[reducible]
def from_as_direct_limit :
  I.as_direct_limit →ₗ[R] I :=
module.direct_limit.lift R _ _ _ (λ i, submodule.of_le i.le) $ λ i j hij r, rfl

@[simps]
def to_as_direct_limit :
  I →ₗ[R] I.as_direct_limit :=
{ to_fun := λ r, module.direct_limit.of R (fg_subideal I) (λ i, i.to_ideal) 
    (λ _ _ h, submodule.of_le h) (principal_fg_subideal r) ⟨r, mem_principal_fg_subideal r⟩,
  map_add' := λ i i', begin 
    set ι : fg_subideal I := doubleton_fg_subideal i i' with ι_eq, 
    rw ←@module.direct_limit.of_f R _ (fg_subideal I) _ _ (λ i, i.to_ideal) _ _ 
        (λ _ _ h, submodule.of_le h) _ _ (add_le_doubleton_fg_subideal i i'),
    simp_rw [submodule.of_le_apply, subtype.coe_mk],
    erw show (⟨i + i', _⟩ : (doubleton_fg_subideal i i').to_ideal) = 
      ⟨i, mem_left_doubleton_fg_subideal _ _⟩ + ⟨i', mem_right_doubleton_fg_subideal _ _⟩, 
      from rfl,
    rw map_add,
    congr' 1,
    { rw ←@module.direct_limit.of_f R _ (fg_subideal I) _ _ (λ i, i.to_ideal) _ _ 
        (λ _ _ h, submodule.of_le h) _ _ (left_le_doubleton_fg_subideal i i'),
      refl, },
    { rw ←@module.direct_limit.of_f R _ (fg_subideal I) _ _ (λ i, i.to_ideal) _ _ 
        (λ _ _ h, submodule.of_le h) _ _ (right_le_doubleton_fg_subideal i i'),
      refl, },
  end,
  map_smul' := λ r i, 
  begin
    rw ←@module.direct_limit.of_f R _ (fg_subideal I) _ _ (λ i, i.to_ideal) _ _ 
        (λ _ _ h, submodule.of_le h) _ _ (principal_fg_subideal_smul r i),
    simpa only [submodule.of_le_apply, ring_hom.id_apply, ←map_smul],
  end }

example : true := trivial

lemma from_to_as_direct_limit :
  function.left_inverse I.from_as_direct_limit I.to_as_direct_limit :=
begin 
  intros z,
  rw to_as_direct_limit_apply,
  rw module.direct_limit.lift_of,
  rw submodule.of_le_apply,
  simp_rw subtype.coe_mk,
  ext,
  rw subtype.coe_mk,
end

lemma to_from_as_direct_limit :
  function.right_inverse I.from_as_direct_limit I.to_as_direct_limit :=
begin 
  intros z,
  induction z using module.direct_limit.induction_on with i z,
  rw module.direct_limit.lift_of,
  rw submodule.of_le_apply,
  rw to_as_direct_limit_apply,
  simp_rw subtype.coe_mk,
  rw ←module.direct_limit.of_f,
  work_on_goal 2 { show _ ≤ i, begin 
    erw submodule.span_le,
    intros r hr,
    rw set.mem_singleton_iff at hr,
    rw subtype.coe_mk at hr,
    rw hr,
    exact z.2,
  end, },
  rw submodule.of_le_apply,
  simp_rw subtype.coe_mk,
  congr' 1,
  ext1,
  refl,
end

@[simps] def iso_as_direct_limit :
  I ≃ₗ[R] I.as_direct_limit :=
{ to_fun := I.to_as_direct_limit,
  map_add' := map_add _,
  map_smul' := map_smul _,
  inv_fun := I.from_as_direct_limit,
  left_inv := I.from_to_as_direct_limit,
  right_inv := I.to_from_as_direct_limit }

-- instance hmmm2 : module R (I.as_direct_limit ⊗[R] M) := tensor_product.left_module

@[simps] def tensor_iso_direct_limit :
  I ⊗[R] M ≃ₗ[R] I.as_direct_limit ⊗[R] M :=
{ inv_fun := (tensor_product.map I.from_as_direct_limit linear_map.id : 
    I.as_direct_limit ⊗[R] M →ₗ[R] I ⊗[R] M),
  left_inv := λ z, 
  begin 
    simp only [linear_map.to_fun_eq_coe],
    rw ←linear_map.comp_apply,
    rw ←tensor_product.map_comp,
    rw linear_map.comp_id,
    convert linear_map.id_apply _,
    convert tensor_product.map_id,
    ext1 z,
    rw linear_map.comp_apply,
    rw I.from_to_as_direct_limit,
    rw linear_map.id_apply,
  end,
  right_inv := λ z,
  begin 
    simp only [linear_map.to_fun_eq_coe],
    rw ←linear_map.comp_apply,
    rw ←tensor_product.map_comp,
    rw linear_map.comp_id,
    convert linear_map.id_apply _,
    convert tensor_product.map_id,
    refine linear_map.ext (λ z, _),
    rw linear_map.comp_apply,
    rw I.to_from_as_direct_limit,
    rw linear_map.id_apply,
  end,
  ..(tensor_product.map I.to_as_direct_limit linear_map.id : 
    I ⊗[R] M →ₗ[R] I.as_direct_limit ⊗[R] M) }

@[reducible]
def as_direct_limit_tensor :=
module.direct_limit (λ (i : fg_subideal I), i.to_ideal ⊗[R] M) 
  (λ i j hij, tensor_product.map (submodule.of_le hij) linear_map.id)

@[reducible]
def iso_as_direct_limit_tensor_aux1 :
  I.as_direct_limit_tensor M ≃ₗ[R] I.as_direct_limit ⊗[R] M :=
@module.direct_limit_of_tensor_product_iso_tensor_product_with_direct_limit R _ 
    (fg_subideal I) _ _ (λ i, i.to_ideal) _ _ (λ _ _ h, submodule.of_le h) M _ _ _ _

end ideal

@[reducible]
def tensor_embedding' :
  module.direct_limit (λ (i : fg_subideal I), (i.to_ideal ⊗[R] M))
    (λ i j hij, tensor_product.map (submodule.of_le hij) linear_map.id : 
      Π (i j : fg_subideal I) (hij : i ≤ j), (i.to_ideal ⊗[R] M) →ₗ[R] (j.to_ideal ⊗[R] M)) →ₗ[R]
  R ⊗[R] M :=
module.direct_limit.lift _ _ _ _ 
  (λ i, Module.tensor_embedding M i.to_ideal) $ λ i j hij z, 
begin
  induction z using tensor_product.induction_on with ii m x y hx hy,
  { simp only [map_zero] },
  { simp only [tensor_product.map_tmul, linear_map.coe_mk, submodule.of_le_apply, 
      linear_map.id_apply, subtype.coe_mk], },
  { simp only [map_add, hx, hy] },
end

lemma tensor_embedding_eq :
  (Module.tensor_embedding M I : I ⊗[R] M →ₗ[R] R ⊗[R] M) = 
  linear_map.comp (tensor_embedding' M I)
    (linear_map.comp (I.iso_as_direct_limit_tensor_aux1 M).symm.to_linear_map 
      ((I.tensor_iso_direct_limit M).to_linear_map)) := 
linear_map.ext $ λ z, begin 
  induction z using tensor_product.induction_on with i m x y hx hy,
  { simp only [map_zero] },
  { simp only [tensor_product.map_tmul, linear_map.comp_apply, linear_map.coe_mk, id,
      linear_equiv.coe_to_linear_map, ideal.tensor_iso_direct_limit_apply,
      module.direct_limit_of_tensor_product_iso_tensor_product_with_direct_limit_symm_apply,
      linear_map.to_fun_eq_coe, ideal.to_as_direct_limit_apply, module.direct_limit.lift_of,
      tensor_product.lift.tmul, linear_map.id_apply, subtype.coe_mk], },
  { simp only [map_add, hx, hy] }
end

example : true := trivial

lemma tensor_embedding_inj_of_fg_inj 
  (hinj : ∀ (I : ideal R), I.fg → function.injective (Module.tensor_embedding M I)) :
  function.injective $ Module.tensor_embedding M I :=
begin 
  rw tensor_embedding_eq,
  refine function.injective.comp _ (function.injective.comp (function.injective.comp _ _) _),
  { refine module.lift_inj R (fg_subideal I) _ _ _ _ _,
    exact λ i, hinj i.to_ideal i.fg, },
  { exact linear_equiv.injective _, },
  { exact linear_equiv.injective _, },
  { exact function.injective_id, },
end
