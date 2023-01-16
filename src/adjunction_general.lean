import algebra.category.Module.basic
import linear_algebra.tensor_product

-- import .hom

open_locale tensor_product

open tensor_product

universes u u' v

variables (R : Type u) (S : Type u') [comm_ring R] [comm_ring S]
variables (X : Type v) [add_comm_group X] [module R X] [module S X]

class bimodule :=
(smul_comm' [] : ∀ (r : R) (s : S) (x : X), r • s • x = s • r • x)

section bimodule

variables {R S X}

lemma bimodule.smul_comm [bimodule R S X] (r : R) (s : S) (x : X) : 
  r • s • x = s • r • x :=
bimodule.smul_comm' r s x

instance bimodule.int (X' : Type v) [add_comm_group X'] [module R X'] :
  bimodule R ℤ X' :=
{ smul_comm' := λ r z x', 
  begin 
    induction z using int.induction_on with n hn n hn,
    { simp, },
    { simpa [add_smul, smul_add] using hn, },
    { simpa [sub_smul, smul_sub] using hn, },
  end }

instance bimodule.symm [bimodule R S X] : bimodule S R X :=
{ smul_comm' := λ s r x, (bimodule.smul_comm r s x).symm } 

end bimodule

section tensor_bimodule

variable [bimodule R S X]
variables (Y : Type v) [add_comm_group Y] [module R Y]

@[simps]
def tensor_bimodule.smul (s : S) : Y →ₗ[R] X →ₗ[R] Y ⊗[R] X :=
{ to_fun := λ y, 
  { to_fun := λ x, y ⊗ₜ (s • x),
    map_add' := λ x x', by rw [smul_add, tmul_add],
    map_smul' := λ r x, by rw [ring_hom.id_apply, smul_tmul', smul_tmul, 
      bimodule.smul_comm] },
  map_add' := λ y y', linear_map.ext $ λ x, by simp [linear_map.add_apply, 
    add_tmul],
  map_smul' := λ r y, linear_map.ext $ λ x, by simp [smul_tmul, tmul_smul] }

lemma tensor_bimodule.one_smul (y : Y) (x : X) : 
  tensor_bimodule.smul R S X Y 1 y x = y ⊗ₜ x := 
begin 
  rw tensor_bimodule.smul_apply_apply,
  rw one_smul,
end

instance tensor_product.bimodule : module S (Y ⊗[R] X) :=
{ smul := λ s, tensor_product.lift $ tensor_bimodule.smul R S X Y s,
  one_smul := λ z,
  begin 
    induction z using tensor_product.induction_on with _ _ a b ha hb,
    { rw [←zero_tmul],
      change tensor_bimodule.smul R S X Y 1 0 0 = 0 ⊗ₜ 0,
      rw tensor_bimodule.one_smul, },
    { change tensor_bimodule.smul R S X Y _ _ _ = _,
      rw tensor_bimodule.one_smul, },
    { change tensor_product.lift _ _ = _ at ha,
      change tensor_product.lift _ _ = _ at hb,
      change tensor_product.lift _ _ = _,
      rw [map_add, ha, hb], },
  end,
  mul_smul := λ s s' z, sorry,
  smul_zero := sorry,
  smul_add := sorry,
  add_smul := sorry,
  zero_smul := sorry }

end tensor_bimodule

section bimodule_hom

variable [bimodule R S X]
variables (Z : Type v) [add_comm_group Z] [module S Z]

instance bimodule_hom : module R (X →ₗ[S] Z) :=
{ smul := λ r l, 
  { to_fun := λ x, l (r • x),
    map_add' := λ _ _, by rw [smul_add, map_add],
    map_smul' := λ s x, by rw [bimodule.smul_comm, map_smul, 
      ring_hom.id_apply] },
  one_smul := sorry,
  mul_smul := sorry,
  smul_zero := sorry,
  smul_add := sorry,
  add_smul := sorry,
  zero_smul := sorry }

end bimodule_hom

namespace Module

@[simps]
def tensor_functor [bimodule R S X] : Module.{v} R ⥤ Module.{v} S :=
{ obj := λ Y, Module.of S (Y ⊗[R] X),
  map := λ Y Y' l, 
  { to_fun := tensor_product.map l linear_map.id,
    map_add' := sorry,
    map_smul' := λ s z, sorry },
  map_id' := sorry,
  map_comp' := sorry }

def hom_functor [bimodule R S X] : Module.{v} S ⥤ Module R :=
{ obj := λ Z, Module.of R $ X →ₗ[S] Z,
  map := λ Z Z' (l : Z →ₗ[S] Z'), 
  { to_fun := λ f, l.comp f,
    map_add' := sorry,
    map_smul' := λ r f, linear_map.ext $ λ x, rfl },
  map_id' := sorry,
  map_comp' := sorry }

end Module