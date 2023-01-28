import algebra.category.Module.abelian

import .tensor_hom

open category_theory category_theory.preadditive 
open tensor_product

open_locale tensor_product

namespace Module

universes u v

variables {R : Type u} [comm_ring R]
variables (M : Module.{v} R)

@[simps]
def hom_functor : Module.{v} R ⥤ Module.{v} R :=
{ obj := λ N, Module.of R $ M ⟶ N,
  map := λ X Y f, 
  { to_fun := λ g, g ≫ f,
    map_add' := λ g g', linear_map.ext $ λ x, by rw add_comp,
    map_smul' := λ r g, linear_map.ext $ λ x, by simp only [ring_hom.id_apply, 
      linear.smul_comp], },
  map_id' := λ X, linear_map.ext $ λ g, linear_map.ext $ λ x, 
    by simp only [linear_map.coe_mk, category.comp_id, id_apply], 
  map_comp' := λ X Y Z g g', linear_map.ext $ λ f, linear_map.ext $ λ x, 
    by simp only [linear_map.coe_mk, coe_comp], }

namespace tensor_left_hom_adj

@[simps]
def hom_equiv.to_fun' {X Y : Module.{v} R} (f : (left_functor M).obj X ⟶ Y) :
  X ⟶ M.hom_functor.obj Y :=
{ to_fun := λ x, 
  { to_fun := λ m, f (x ⊗ₜ m),
    map_add' := λ m m', by rw [tmul_add, map_add],
    map_smul' := λ r m, by rw [ring_hom.id_apply, tmul_smul, map_smul] },
  map_add' := λ x x', linear_map.ext $ λ m, 
    by simp only [linear_map.coe_mk, linear_map.add_apply, add_tmul, map_add],
  map_smul' := λ r x, linear_map.ext $ λ m, 
    by simp only [linear_map.coe_mk, ring_hom.id_apply, linear_map.smul_apply,
      ←smul_tmul', map_smul], }

@[reducible]
def hom_equiv.inv_fun' {X Y : Module.{v} R} (f : X ⟶ M.hom_functor.obj Y) :
  (left_functor M).obj X ⟶ Y :=
tensor_product.lift 
{ to_fun := λ x, 
  { to_fun := λ m, (f x).to_fun m,
    map_add' := λ m m', by simp only [linear_map.to_fun_eq_coe, map_add],
    map_smul' := λ r m, by simp only [linear_map.to_fun_eq_coe, 
      linear_map.map_smulₛₗ], },
  map_add' := λ x x', linear_map.ext $ λ m, 
    by simp only [linear_map.to_fun_eq_coe, map_add, linear_map.mk_coe],
  map_smul' := λ r x, linear_map.ext $ λ m, 
    by simp only [linear_map.to_fun_eq_coe, linear_map.map_smulₛₗ, 
      linear_map.mk_coe], }

@[simps]
def hom_equiv (X Y : Module.{v} R) :
  ((left_functor M).obj X ⟶ Y) ≃ (X ⟶ M.hom_functor.obj Y) :=
{ to_fun := hom_equiv.to_fun' M,
  inv_fun := hom_equiv.inv_fun' M,
  left_inv := λ f, linear_map.ext $ λ z, 
  begin 
    induction z using tensor_product.induction_on with x m a b ha hb,
    { simp only [map_zero], },
    { simp only [tensor_product.lift.tmul, linear_map.coe_mk, 
        linear_map.to_fun_eq_coe, hom_equiv.to_fun'_apply_apply], },
    { rw [map_add, ha, hb, map_add], }
  end,
  right_inv := λ f, linear_map.ext $ λ x, linear_map.ext $ λ m,
  by simp only [hom_equiv.to_fun'_apply_apply, tensor_product.lift.tmul,
      linear_map.coe_mk, linear_map.to_fun_eq_coe], }

@[simps]
def unit : 𝟭 (Module.{v} R) ⟶ left_functor M ⋙ M.hom_functor :=
{ app := λ X, 
  { to_fun := λ (x : X), 
    { to_fun := λ m, x ⊗ₜ m,
      map_add' := tmul_add _,
      map_smul' := λ _ _, tmul_smul _ _ _ },
    map_add' := λ (x x' : X), linear_map.ext $ λ m, 
      by simp only [linear_map.add_apply, linear_map.coe_mk, add_tmul],
    map_smul' := λ r (x : X), linear_map.ext $ λ m, 
      by simp only [ring_hom.id_apply, linear_map.smul_apply, linear_map.coe_mk,
        ←smul_tmul'], },
  naturality' := λ X Y f, linear_map.ext $ λ (x : X), linear_map.ext $ λ m, 
    by simp }

@[simps]
def counit : M.hom_functor ⋙ left_functor M ⟶ 𝟭 (Module R) :=
{ app := λ X, tensor_product.lift 
  { to_fun := λ (f : M →ₗ[R] X), f,
    map_add' := λ _ _, rfl,
    map_smul' := λ r x, rfl },
  naturality' := λ X Y f, linear_map.ext $ λ z, 
  begin 
    induction z using tensor_product.induction_on with g m a b ha hb,
    { simp only [map_zero] },
    { simp [lift.tmul], },
    { rw [map_add, map_add, ha, hb], },
  end }

end tensor_left_hom_adj

@[simps]
def tensor_left_hom_adj : tensor_product.left_functor M ⊣ hom_functor M :=
{ hom_equiv := tensor_left_hom_adj.hom_equiv M,
  unit := tensor_left_hom_adj.unit M,
  counit := tensor_left_hom_adj.counit M,
  hom_equiv_unit' := λ X Y (f : (X ⊗[R] M) →ₗ[R] Y), rfl,
  hom_equiv_counit' := λ X Y g, linear_map.ext $ λ z,
  begin 
    induction z using tensor_product.induction_on with m x a b ha hb,
    { simp only [map_zero] },
    { simp },
    { rw [map_add, map_add, ha, hb], },
  end }

end Module
