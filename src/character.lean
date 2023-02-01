import algebra.category.Module.change_of_rings
import algebra.group.ulift
import group_theory.quotient_group
import data.rat.basic
import category_theory.preadditive.injective

import .adjunction_general

open category_theory
open_locale tensor_product

universes u v w w'

@[derive add_comm_group]
def rat_circle : Type* :=
  ulift $ ℚ ⧸ (algebra_map ℤ ℚ).to_add_monoid_hom.range

instance rat_circle.inj : injective (AddCommGroup.of rat_circle) := sorry

section character_module

variables {R : Type u} [comm_ring R] 
variables (M : Type w) [add_comm_group M] [module R M]
variables (N : Type w) [add_comm_group N] [module R N]
variables (N' : Type w) [add_comm_group N'] [module R N']

@[derive add_comm_group]
def character_module : Type w :=
M →ₗ[ℤ] rat_circle.{w}

instance character_module.coe_to_fun : has_coe_to_fun (character_module M) (λ _, M → rat_circle) :=
{ coe := λ f, f.to_fun }

instance character_module.add_monoid_hom_class :
  add_monoid_hom_class (character_module M) M rat_circle :=
{ coe := λ f, f,
  coe_injective' := λ f g h, linear_map.ext $ λ x, congr_fun h _,
  map_add := λ f, f.map_add,
  map_zero := λ f, f.map_zero }

instance character_module.has_smul : has_smul R (character_module M) :=
{ smul := λ r f, 
  { to_fun := λ m, f (r • m),
    map_add' := λ x y, by rw [smul_add, map_add],
    map_smul' := λ z x, by rw [ring_hom.id_apply, ←f.map_smul, smul_comm] } }

@[simp] lemma character_module.smul_apply (r : R) (f : character_module M) (m : M) :
  (r • f) m = f (r • m) := rfl

instance character_module.mul_action : mul_action R (character_module M) :=
{ one_smul := λ f, linear_map.ext $ λ x, by rw [character_module.smul_apply, one_smul],
  mul_smul := λ a b f, linear_map.ext $ λ x, 
    by rw [character_module.smul_apply, mul_comm, mul_smul, character_module.smul_apply, character_module.smul_apply],
  ..character_module.has_smul M}

instance character_module.distrib_mul_action : distrib_mul_action R (character_module M) :=
{ smul_zero := λ r, linear_map.ext $ λ x, 
    by rw [character_module.smul_apply, linear_map.zero_apply, linear_map.zero_apply],
  smul_add := λ r f g, linear_map.ext $ λ x,
    by rw [character_module.smul_apply, linear_map.add_apply, linear_map.add_apply,
      character_module.smul_apply, character_module.smul_apply],
  ..character_module.mul_action M}

instance character_module.module : module R (character_module M) :=
{ add_smul := λ a b f, linear_map.ext $ λ x, 
    by simp only [character_module.smul_apply, add_smul, linear_map.add_apply, map_add],
  zero_smul := λ f, linear_map.ext $ λ x, 
    by simp only [character_module.smul_apply, zero_smul, map_zero, linear_map.zero_apply],
  ..character_module.distrib_mul_action M}

namespace character_module

section map

variables {M N}

@[simps apply]
def map (L : M →ₗ[R] N) : character_module N →ₗ[R] character_module M :=
{ to_fun := λ f, 
  { to_fun := λ m, f $ L m,
    map_add' := λ m m', by rw [map_add, map_add],
    map_smul' := λ z m, by rw [ring_hom.id_apply, map_zsmul, f.map_smul] },
  map_add' := λ f g, linear_map.ext $ λ x, by simp,
  map_smul' := λ r f, linear_map.ext $ λ x, by simp }

end map

lemma map_id : 
  map (linear_map.id : M →ₗ[R] M) = 
  (linear_map.id : character_module M →ₗ[R] character_module M) :=
linear_map.ext $ λ f, linear_map.ext $ λ x, by simp

section map

variables {M N N'}

lemma map_comp (L : M →ₗ[R] N) (L' : N →ₗ[R] N') :
  map (L'.comp L) = (map L).comp (map L') :=
linear_map.ext $ λ f, linear_map.ext $ λ x, by simp

lemma map_inj (L : M →ₗ[R] N) (hL : function.injective L) :
  function.surjective (map L) :=
λ g, ⟨begin 
  haveI : mono (AddCommGroup.of_hom L.to_add_monoid_hom) :=
    by rwa AddCommGroup.mono_iff_injective,
  refine add_monoid_hom.to_int_linear_map 
    (injective.factor_thru (AddCommGroup.of_hom g.to_add_monoid_hom) 
    (AddCommGroup.of_hom L.to_add_monoid_hom)),
end, begin 
  ext x : 1,
  haveI : mono (AddCommGroup.of_hom L.to_add_monoid_hom) :=
    by rwa AddCommGroup.mono_iff_injective,
  rw [map_apply, linear_map.coe_mk, add_monoid_hom.coe_to_int_linear_map],
  exact fun_like.congr_fun (injective.comp_factor_thru (AddCommGroup.of_hom g.to_add_monoid_hom)
    (AddCommGroup.of_hom L.to_add_monoid_hom)) x,
end⟩

end map

def functor : (Module.{max u v} R)ᵒᵖ ⥤ Module.{max u v} R :=
{ obj := λ M, Module.of R $ character_module M.unop,
  map := λ M N L, map L.unop,
  map_id' := λ M, map_id M.unop,
  map_comp' := λ M N N' L L', map_comp L'.unop L.unop }

@[simps]
def hom_equiv : (N →ₗ[R] character_module M) ≃ (character_module $ N ⊗[R] M) := 
{ to_fun := λ f, add_monoid_hom.to_int_linear_map $ tensor_product.to_add_comm_group' R (λ p, f p.1 p.2) 
    (λ m, by rw [map_zero, linear_map.zero_apply]) 
    (λ n, by rw [map_zero]) (λ m n n', by rw [map_add, linear_map.add_apply]) 
    (λ n m m', by rw [map_add]) $ λ r n m, by simpa only [map_smul],
  inv_fun := λ g, 
  { to_fun := λ n, 
    { to_fun := λ m, g (n ⊗ₜ m),
      -- map_zero' := by rw [tensor_product.tmul_zero, map_zero],
      map_add' := λ m m', by rw [tensor_product.tmul_add, map_add],
      map_smul' := λ z m, by rw [ring_hom.id_apply, ←map_zsmul, tensor_product.smul_tmul', 
        tensor_product.smul_tmul] },
    map_add' := λ n n', linear_map.ext $ λ m, by simp only [linear_map.coe_mk, 
      tensor_product.add_tmul, map_add, linear_map.add_apply],
    map_smul' := λ r n, linear_map.ext $ λ m, by simp only [linear_map.coe_mk, 
      ring_hom.id_apply, character_module.smul_apply, tensor_product.smul_tmul], },
  left_inv := λ f, linear_map.ext $ λ n, linear_map.ext $ λ m, by simp only [linear_map.coe_mk, 
    add_monoid_hom.coe_to_int_linear_map, tensor_product.to_add_comm_group'.apply_tmul],
  right_inv := λ g,
  begin 
    ext1 z,
    induction z using tensor_product.induction_on with m n z z' hz hz',
    { simp only [map_zero] },
    { simp only [linear_map.coe_mk, tensor_product.to_add_comm_group'.apply_tmul,
        add_monoid_hom.coe_to_int_linear_map], },
    { rw [map_add, hz, hz', map_add] },
  end
   }

@[reducible]
noncomputable def aux1_finite_order  
  {m : M} (hm : m ≠ 0) (hm_order : add_order_of m ≠ 0)
  (k : ℤ) : rat_circle :=
ulift.up $ quotient_add_group.mk' _ (rat.mk k $ add_order_of m)

lemma aux1_finite_order.map_add {m : M} (hm : m ≠ 0) (hm_order : add_order_of m ≠ 0)
  (k k' : ℤ) : 
  aux1_finite_order M hm hm_order (k + k') = 
  aux1_finite_order M hm hm_order k + aux1_finite_order M hm hm_order k' :=
begin 
  ext1,
  erw quotient_add_group.mk'_eq_mk',
  refine ⟨_, ⟨0, rfl⟩, _⟩,
  erw add_zero,
  rw rat.add_mk,
end

lemma aux1_finite_order.map_zsmul {m : M} (hm : m ≠ 0) (hm_order : add_order_of m ≠ 0)
  (k k' : ℤ) : 
  aux1_finite_order M hm hm_order (k * k') = 
  k • aux1_finite_order M hm hm_order k' :=
begin 
  ext1,
  erw quotient_add_group.mk'_eq_mk',
  refine ⟨_, ⟨0, rfl⟩, _⟩,
  erw add_zero,
  rw zsmul_eq_mul,
  rw rat.coe_int_eq_mk,
  rw rat.mul_def,
  work_on_goal 2 { norm_num },
  work_on_goal 2 { exact_mod_cast hm_order },
  rw one_mul,
end

lemma aux1_finite_order_wd' {m : M} (hm : m ≠ 0) (hm_order : add_order_of m ≠ 0)
  (k k' : ℤ) (EQ : k • m = k' • m) :
  aux1_finite_order M hm hm_order k = aux1_finite_order M hm hm_order k' :=
begin 
  ext1,
  rw quotient_add_group.mk'_eq_mk',
  have EQ' : |k - k'| • m = 0,
  { rcases abs_choice (k - k') with h|h; 
    rw h;
    try { rw neg_sub };
    rw sub_smul;
    rw EQ;
    rw sub_self, },
  obtain ⟨z, hz⟩ := add_order_of_dvd_iff_zsmul_eq_zero.mpr EQ',
  suffices : ∃ (z : ℚ) (H : z ∈ (algebra_map ℤ ℚ).to_add_monoid_hom.range),
    rat.mk (|k - k'|) ↑(add_order_of m) = z,
  { obtain ⟨_, ⟨z, rfl⟩, (h : _ = (z : ℚ))⟩ := this,
    rcases abs_choice (k - k') with h'|h',
    { rw h' at h, 
      rw [sub_eq_add_neg, rat.add_mk, ←rat.neg_def, add_neg_eq_iff_eq_add] at h,
      rw h,
      refine ⟨_, ⟨-z, rfl⟩, _⟩,
      change _ + -(z : ℚ) = _,
      abel, },
    { rw h' at h,
      rw [←rat.neg_def, sub_eq_add_neg, rat.add_mk, neg_eq_iff_neg_eq, ←rat.neg_def] at h,
      replace h := h.symm,
      rw [add_neg_eq_iff_eq_add] at h,
      rw h,
      refine ⟨_, ⟨z, rfl⟩, _⟩,
      change _ + _ + (z : ℚ) = _,
      abel, }, },
  refine ⟨_, ⟨z, rfl⟩, _⟩,
  rw hz,
  change _ = (z : ℚ),
  rw rat.coe_int_eq_mk,
  rw rat.mk_eq,
  { ring },
  { exact_mod_cast hm_order },
  { norm_num },
end

@[simps]
noncomputable def morphism_finite_order {m : M} (hm : m ≠ 0) (hm_order : add_order_of m ≠ 0) :
  (submodule.span ℤ {m} : submodule ℤ M) →ₗ[ℤ] rat_circle :=
{ to_fun := λ m', aux1_finite_order M hm hm_order (submodule.mem_span_singleton.mp m'.2).some,
  map_add' := λ m' m'', 
  begin 
    generalize_proofs h1 h2 h3,
    have EQ : (h2.some + h3.some) • m = h1.some • m,
    { rw [add_smul, h2.some_spec, h3.some_spec, h1.some_spec], refl, },
    rw ←aux1_finite_order_wd' M hm hm_order _ _ EQ,
    rw aux1_finite_order.map_add,
  end,
  map_smul' := λ z m', 
  begin 
    generalize_proofs h1 h2,
    have EQ : (z * h2.some) • m = h1.some • m,
    { rw [mul_smul, h2.some_spec, h1.some_spec], refl, },
    rw ←aux1_finite_order_wd' M hm hm_order _ _ EQ,
    rw ring_hom.id_apply,
    rw aux1_finite_order.map_zsmul,
  end }

lemma morphism_finite_order.apply_m {m : M} (hm : m ≠ 0) (hm_order : add_order_of m ≠ 0) :
  morphism_finite_order M hm hm_order ⟨m, submodule.mem_span_singleton_self _⟩ ≠ 0 := 
begin 
  rw morphism_finite_order_apply,
  generalize_proofs h1 h2,
  rw show aux1_finite_order M hm hm_order h2.some = aux1_finite_order M hm hm_order 1,
  { rw aux1_finite_order_wd', rw [h2.some_spec, one_smul] },
  change ¬ _,
  rw (ulift.ext_iff _ _).not,
  erw quotient_add_group.eq_zero_iff,
  rintros ⟨z, (hz : (z : ℚ) = _)⟩,
  rw rat.coe_int_eq_mk at hz,
  rw rat.mk_eq at hz,
  work_on_goal 2 { norm_num },
  work_on_goal 2 { exact_mod_cast hm_order },
  rw [one_mul] at hz,
  rw int.mul_eq_one_iff_eq_one_or_neg_one at hz,
  rcases hz with ⟨rfl, hz⟩|⟨rfl, hz⟩,
  { refine hm (add_monoid.order_of_eq_one_iff.mp _),
    exact_mod_cast hz, },
  { have rid := int.coe_nat_nonneg (add_order_of m),
    rw hz at rid,
    linarith only [rid], },
end

@[reducible]
noncomputable def aux1_infinite_order  
  {m : M} (hm : m ≠ 0) (hm_order : add_order_of m = 0)
  (k : ℤ) : rat_circle :=
ulift.up $ quotient_add_group.mk' _ (rat.mk k 37)

lemma aux1_infinite_order.eq_zero {m : M} (hm : m ≠ 0) (hm_order : add_order_of m = 0)
  (k : ℤ) (hk : k • m = 0) : k = 0 :=
begin 
  by_contra rid,
  have : int.nat_abs k • m = 0,
  { suffices : (int.nat_abs k : ℤ) • m = 0,
    { exact_mod_cast this },
    rw ←int.abs_eq_nat_abs,
    rcases abs_choice k with h|h;
    rw h;
    try { rw neg_smul };
    rw hk,
    rw neg_zero },
  refine add_order_of_eq_zero_iff'.mp hm_order k.nat_abs _ this,
  exact int.nat_abs_pos_of_ne_zero rid,
end

lemma aux1_infinite_order_wd' {m : M} (hm : m ≠ 0) (hm_order : add_order_of m = 0)
  (k k' : ℤ) (hk : k • m = k' • m) : k = k' :=
begin 
  have EQ : (k - k') • m = 0,
  { rw [sub_smul, hk, sub_self] },
  rw ←int.sub_eq_zero_iff_eq,
  exact aux1_infinite_order.eq_zero M hm hm_order _ EQ,
end

@[simps]
noncomputable def morphism_infinite_order {m : M} (hm : m ≠ 0) (hm_order : add_order_of m = 0) :
  (submodule.span ℤ {m} : submodule ℤ M) →ₗ[ℤ] rat_circle :=
{ to_fun := λ m', aux1_infinite_order M hm hm_order (submodule.mem_span_singleton.mp m'.2).some,
  map_add' := λ m' m'', 
  begin 
    generalize_proofs h1 h2 h3,
    have EQ : (h2.some + h3.some) • m = h1.some • m,
    { rw [add_smul, h2.some_spec, h3.some_spec, h1.some_spec], refl, },
    rw ←aux1_infinite_order_wd' M hm hm_order _ _ EQ,
    ext1,
    erw quotient_add_group.mk'_eq_mk',
    refine ⟨_, ⟨0, rfl⟩, _⟩,
    erw add_zero,
    rw rat.add_mk,
  end,
  map_smul' := λ z m', 
  begin 
    generalize_proofs h1 h2,
    have EQ : (z * h2.some) • m = h1.some • m,
    { rw [mul_smul, h2.some_spec, h1.some_spec], refl, },
    rw ←aux1_infinite_order_wd' M hm hm_order _ _ EQ,
    rw ring_hom.id_apply,
    ext1,
    erw quotient_add_group.mk'_eq_mk',
    refine ⟨_, ⟨0, rfl⟩, _⟩,
    erw add_zero,
    rw zsmul_eq_mul,
    rw rat.coe_int_eq_mk,
    rw rat.mul_def,
    work_on_goal 2 { norm_num },
    work_on_goal 2 { norm_num },
    rw one_mul,
  end }

lemma morphism_infinite_order.apply_m {m : M} (hm : m ≠ 0) (hm_order : add_order_of m = 0) :
  morphism_infinite_order M hm hm_order ⟨m, submodule.mem_span_singleton_self _⟩ ≠ 0 :=
begin 
  rw morphism_infinite_order_apply,
  generalize_proofs h1 h2,
  rw show aux1_infinite_order M hm hm_order h2.some = aux1_infinite_order M hm hm_order 1,
  { rw aux1_infinite_order_wd' M hm hm_order h2.some 1 _, rw [h2.some_spec, one_smul] },
  change ¬ _,
  rw (ulift.ext_iff _ _).not,
  erw quotient_add_group.eq_zero_iff,
  rintros ⟨z, (hz : (z : ℚ) = _)⟩,
  rw rat.coe_int_eq_mk at hz,
  rw rat.mk_eq at hz,
  work_on_goal 2 { norm_num },
  work_on_goal 2 { norm_num },
  rw [one_mul] at hz,
  rw int.mul_eq_one_iff_eq_one_or_neg_one at hz,
  rcases hz with ⟨rfl, hz⟩|⟨rfl, hz⟩,
  { linarith, },
  { linarith, },
end 

lemma non_zero {m : M} (hm : m ≠ 0) : ∃ (h : character_module M), h m ≠ 0 :=
begin 
  let M' : submodule ℤ M := submodule.span ℤ {m},
  suffices : ∃ (h' : M' →ₗ[ℤ] rat_circle), h' ⟨m, submodule.subset_span (set.mem_singleton _)⟩ ≠ 0,
  { obtain ⟨h', hh'⟩ := this,
    let ι : AddCommGroup.of M' ⟶ AddCommGroup.of M := ⟨λ m, m.1, rfl, λ _ _, rfl⟩,
    haveI : mono ι,
    { refine concrete_category.mono_of_injective _ subtype.val_injective, },
    let f' : AddCommGroup.of M ⟶ AddCommGroup.of rat_circle :=
      injective.factor_thru (show AddCommGroup.of M' ⟶ AddCommGroup.of rat_circle, 
      from h'.to_add_monoid_hom) ι,
    refine ⟨add_monoid_hom.to_int_linear_map $ show M →+ rat_circle, from f', _⟩,
    have eq0 : _ ≫ f' = _ := injective.comp_factor_thru _ _,
    erw fun_like.congr_fun eq0 ⟨m, submodule.subset_span (set.mem_singleton _)⟩,
    exact hh' },
  by_cases h_order : add_order_of m ≠ 0,
  { exact ⟨morphism_finite_order _ hm h_order, morphism_finite_order.apply_m _ hm h_order⟩, },
  { exact ⟨morphism_infinite_order _ hm (by rwa [not_ne_iff] at h_order), 
      morphism_infinite_order.apply_m _ hm (by rwa [not_ne_iff] at h_order)⟩ },
end

end character_module

end character_module