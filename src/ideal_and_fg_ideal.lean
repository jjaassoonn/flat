import algebra.direct_limit
import algebra.category.fgModule.basic

import .flat'
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
λ _, infer_instance

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

instance hmmm2 : module R (I.as_direct_limit ⊗[R] M) := tensor_product.left_module

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
  (λ i, tensor_product.map ⟨coe, λ _ _, rfl, λ _ _, rfl⟩ linear_map.id) $ λ i j hij z, 
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

#exit

open_locale tensor_product

instance all_are_abelian1 : Π (i : fg_subideal I), add_comm_group $ i.to_ideal ⊗[R] M := 
λ i, infer_instance

variable {I}

@[reducible] def fg_subideal.map_of_le (i j : fg_subideal I) (hij : i ≤ j) :
  (i.to_ideal ⊗[R] M) →ₗ[R] (j.to_ideal ⊗[R] M) :=
tensor_product.map (submodule.of_le hij) linear_map.id

variable (I)
@[derive [add_comm_monoid, module R]]
def ideal.tensor_as_direct_limit : Type u :=
module.direct_limit (λ (J : fg_subideal I), J.to_ideal ⊗[R] M) $ λ i j hij, i.map_of_le M _ hij

@[reducible]
def ideal.from_tensor_as_direct_limit :
  I.tensor_as_direct_limit M →ₗ[R] I ⊗[R] M :=
module.direct_limit.lift R _ _ _ (λ i, tensor_product.map (submodule.of_le i.le) linear_map.id) $
λ i j hij z, 
begin 
  induction z using tensor_product.induction_on with x m a b ha hb,
  { simp only [map_zero] },
  { simpa only [tensor_product.map_tmul, submodule.of_le_apply, linear_map.id_apply, 
      subtype.coe_mk], },
  { rw [map_add, map_add, ha, hb, map_add], },
end

lemma ideal.from_tensor_as_direct_limit_inj :
  function.injective $ I.from_tensor_as_direct_limit M :=
begin 
  simp_rw [←linear_map.ker_eq_bot, submodule.eq_bot_iff, linear_map.mem_ker],
  intros z hz,
  induction z using module.direct_limit.induction_on with i z,
  induction z using tensor_product.induction_on with x m a b ha hb,
  { simp only [map_zero] },
  { rw [module.direct_limit.lift_of, tensor_product.map_tmul, linear_map.id_apply] at hz,
    rw ←module.direct_limit.of_f,
    work_on_goal 3 { exact i },
    work_on_goal 2 { exact le_refl _ },
    
    -- have := module.direct_limit.of.zero_exact,
     },
end

#exit

@[ext]
structure fg_submodule :=
(to_submodule : submodule R M)
(fg : to_submodule.fg)

instance : preorder (fg_submodule R M) :=
preorder.lift fg_submodule.to_submodule

variables {R M}
lemma fg_submodule.le_iff (x y : fg_submodule R M) : x ≤ y ↔ x.to_submodule ≤ y.to_submodule := 
iff.rfl

instance : is_directed (fg_submodule R M) (≤) :=
{ directed := λ x y, ⟨⟨x.to_submodule ⊔ y.to_submodule, submodule.fg.sup x.fg y.fg⟩, 
    ⟨show x.to_submodule ≤ x.to_submodule ⊔ y.to_submodule, from le_sup_left, 
     show y.to_submodule ≤ x.to_submodule ⊔ y.to_submodule, from le_sup_right⟩⟩ }

instance : nonempty (fg_submodule R M) :=
nonempty.intro $ ⟨⊥, submodule.fg_bot⟩

variables (I : ideal R)

variable [∀ (I : ideal R), decidable_eq $ fg_submodule R I]

@[derive [add_comm_monoid, module R]]
def ideal.as_direct_limit : Type u := 
module.direct_limit (λ (x : fg_submodule R I), x.to_submodule)
    (λ i j hij, submodule.of_le hij)

@[reducible]
def ideal.from_as_direct_limit :
  I.as_direct_limit →ₗ[R] I :=
module.direct_limit.lift _ _ _ _ (λ i, ⟨coe, λ _ _, rfl, λ _ _, rfl⟩) $ 
  λ i j (hij : i.to_submodule ≤ j.to_submodule) x, 
  by simp only [linear_map.coe_mk, submodule.coe_of_le]

lemma ideal.from_as_direct_limit.inj_aux 
  (x : I.as_direct_limit) (hx : I.from_as_direct_limit x = 0) :
  x = 0 :=
begin 
  induction x using module.direct_limit.induction_on with i x,
  rw module.direct_limit.lift_of at hx,
  rw linear_map.coe_mk at hx,
  rw show x = 0, by exact_mod_cast hx,
  rw map_zero,  
end

lemma ideal.from_as_direct_limit.inj :
  function.injective I.from_as_direct_limit :=
begin 
  rw ←linear_map.ker_eq_bot,
  rw eq_bot_iff,
  intros x hx,
  rw linear_map.mem_ker at hx,
  rw submodule.mem_bot,
  apply ideal.from_as_direct_limit.inj_aux,
  assumption,
end

lemma ideal.from_as_direct_limit.surj :
  function.surjective I.from_as_direct_limit :=
begin 
  intros x,
  set i : fg_submodule R I := ⟨submodule.span _ {x}, submodule.fg_span_singleton _⟩ with i_eq,
  set fi : _ →ₗ[R] I.as_direct_limit := module.direct_limit.of R _ _ _ i with fi_eq,
  refine ⟨fi ⟨x, submodule.mem_span_singleton_self _⟩, _⟩,
  rw module.direct_limit.lift_of,
  rw linear_map.coe_mk,
  refl,
end

lemma ideal.from_as_direct_limit.bij :
  function.bijective I.from_as_direct_limit := 
⟨by apply ideal.from_as_direct_limit.inj, by apply ideal.from_as_direct_limit.surj⟩

@[reducible]
noncomputable def ideal.iso_as_direct_limit' :
  I.as_direct_limit ≃ₗ[R] I :=
linear_equiv.of_bijective _ (ideal.from_as_direct_limit.bij I)

@[reducible]
noncomputable def ideal.iso_as_direct_limit : I ≃ₗ[R] I.as_direct_limit :=
I.iso_as_direct_limit'.symm

lemma ideal.iso_as_direct_limit_apply (x : I) : 
  I.iso_as_direct_limit x = 
  let i : fg_submodule R I := ⟨submodule.span R {x}, submodule.fg_span_singleton _⟩ in
  (show _ →ₗ[R] I.as_direct_limit, from module.direct_limit.of R _ _ _  i) 
  ⟨x, submodule.mem_span_singleton_self _⟩ := 
begin 
  apply_fun I.iso_as_direct_limit' using ideal.from_as_direct_limit.inj I,
  rw linear_equiv.apply_symm_apply,
  rw linear_equiv.of_bijective_apply,
  rw module.direct_limit.lift_of,
  refl,
end

open_locale tensor_product

instance aux1 : module R (R ⊗[R] M) := tensor_product.left_module
instance aux2 : module R (I.as_direct_limit ⊗[R] M) := tensor_product.left_module

variables (M)

@[reducible]
def tensor_embedding' (I : ideal R) :
  (I.as_direct_limit ⊗[R] M) →ₗ[R] (R ⊗[R] M) :=
tensor_product.map (module.direct_limit.lift _ _ _ _ (λ i, ⟨coe, λ _ _, rfl, λ _ _, rfl⟩) $ 
  λ i j hij x, rfl) linear_map.id

instance : has_mem R (fg_submodule R I) :=
{ mem := λ r x, r ∈ (coe : I → R) '' x.to_submodule }

variables {M I}
@[simps]
def fg_submodule.to_ideal (i : fg_submodule R I) : ideal R :=
{ carrier := { r | r ∈ i },
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry }

lemma fg_submodule.to_ideal_fg (i : fg_submodule R I) : i.to_ideal.fg := sorry

@[simps]
noncomputable def some_iso : I.as_direct_limit ⊗[R] M ≃ₗ[R] I ⊗[R] M :=
{ to_fun := tensor_product.map I.from_as_direct_limit linear_map.id,
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := tensor_product.map I.iso_as_direct_limit.to_linear_map linear_map.id,
  left_inv := sorry,
  right_inv := sorry }

lemma some_lemma : 
  Module.tensor_embedding M I = (tensor_embedding' M I).comp 
    some_iso.symm.to_linear_map :=
linear_map.ext $ λ z, begin 
  induction z using tensor_product.induction_on with i m x y hx hy,
  { simp only [map_zero] },
  { simp only [linear_map.coe_mk, linear_map.comp_apply, linear_map.coe_mk, 
      linear_equiv.coe_to_linear_map, some_iso_symm_apply, tensor_product.map_tmul],
    rw ideal.iso_as_direct_limit_apply,
    rw module.direct_limit.lift_of,
    simp only [linear_map.coe_mk, linear_map.id_apply],
    refl, },
  { rw [map_add, hx, hy, map_add], },
end

instance aux4 (i : fg_submodule R I) : module R (i.to_submodule ⊗[R] M) := tensor_product.left_module
instance aux5 : module R (I ⊗[R] M) := tensor_product.left_module

variable (M)
@[reducible]
def another_morphism (i : fg_submodule R I) : 
  i.to_submodule ⊗[R] M →ₗ[R] I.as_direct_limit ⊗[R] M :=
tensor_product.map (module.direct_limit.of R _ _ _ i) linear_map.id

lemma another_morphism.inj (i : fg_submodule R I) :
  function.injective (another_morphism M i) :=
begin 
  rw ←linear_map.ker_eq_bot,
  rw submodule.eq_bot_iff,
  simp_rw linear_map.mem_ker,
  intros z hz,
  induction z using tensor_product.induction_on with x m a b ha hb,
  { refl, },
  { rw tensor_product.map_tmul at hz,
    rw linear_map.id_apply at hz,
     },
end

example (i : fg_submodule R I) : true :=
begin 
  have : i.to_submodule →ₗ[R] I.as_direct_limit := module.direct_limit.of R _ _ _ i,
end

lemma tensor_embedding'.inj (I : ideal R)
  (hfg : ∀ (I : ideal R), I.fg → function.injective (Module.tensor_embedding M I)) :
  function.injective (tensor_embedding' M I) :=
begin 
  have hfg' := hfg,
  simp_rw [←linear_map.ker_eq_bot, submodule.eq_bot_iff, linear_map.mem_ker] at hfg ⊢,
  intros z hz,
  induction z using tensor_product.induction_on with z m hx hy,
  { simp only [map_zero], },
  { rw [tensor_product.map_tmul, linear_map.id_apply] at hz,
    induction z using module.direct_limit.induction_on with i z,
    rw [module.direct_limit.lift_of, linear_map.coe_mk] at hz,
    
    -- apply_fun some_iso,
    -- work_on_goal 2 { exact equiv_like.injective some_iso },
    -- rw some_iso_apply,
    -- rw tensor_product.map_tmul,
    -- rw module.direct_limit.lift_of,
    -- rw linear_map.coe_mk,
    -- rw linear_map.id_apply,
    -- -- erw hz,
    -- rw map_zero,
    
    -- -- convert hfg,
    -- -- convert hfg,
    -- -- have := @module.direct_limit.of_f R _ (fg_submodule R I),
     },
end

example (hI : ∀ (I : ideal R), I.fg → function.injective (Module.tensor_embedding M I))
  (J : ideal R) : 
  function.injective (Module.tensor_embedding M J) :=
begin 

end