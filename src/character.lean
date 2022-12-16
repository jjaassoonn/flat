import algebra.category.Module.change_of_rings
import algebra.group.ulift
import group_theory.quotient_group
import data.rat.basic
import category_theory.preadditive.injective

open category_theory

universes u

@[derive add_comm_group]
def rat_circle : Type u :=
  ulift $ ℚ ⧸ (algebra_map ℤ ℚ).to_add_monoid_hom.range

instance rat_circle.inj : injective (AddCommGroup.of rat_circle) := sorry


section character_module

variables {R : Type u} [comm_ring R] 
variables (M : Type u) [add_comm_group M] [module R M]
variables (N : Type u) [add_comm_group N] [module R N]
variables (N' : Type u) [add_comm_group N'] [module R N']

@[derive add_comm_group]
def character_module : Type u :=
M →+ rat_circle.{u}

instance character_module.coe_to_fun : has_coe_to_fun (character_module M) (λ _, M → rat_circle.{u}) :=
{ coe := λ f, f.to_fun }

instance character_module.add_monoid_hom_class :
  add_monoid_hom_class (character_module M) M rat_circle.{u} :=
{ coe := λ f, f,
  coe_injective' := λ f g h, add_monoid_hom.ext $ λ x, congr_fun h _,
  map_add := λ f, f.map_add,
  map_zero := λ f, f.map_zero }

instance character_module.has_smul : has_smul R (character_module M) :=
{ smul := λ r f, 
  { to_fun := λ m, f (r • m),
    map_zero' := by rw [smul_zero, map_zero],
    map_add' := λ x y, by rw [smul_add, map_add] } }

@[simp] lemma character_module.smul_apply (r : R) (f : character_module M) (m : M) :
  (r • f) m = f (r • m) := rfl

instance character_module.mul_action : mul_action R (character_module M) :=
{ one_smul := λ f, add_monoid_hom.ext $ λ x, by rw [character_module.smul_apply, one_smul],
  mul_smul := λ a b f, add_monoid_hom.ext $ λ x, 
    by rw [character_module.smul_apply, mul_comm, mul_smul, character_module.smul_apply, character_module.smul_apply],
  ..character_module.has_smul M}

instance character_module.distrib_mul_action : distrib_mul_action R (character_module M) :=
{ smul_zero := λ r, add_monoid_hom.ext $ λ x, 
    by rw [character_module.smul_apply, add_monoid_hom.zero_apply, add_monoid_hom.zero_apply],
  smul_add := λ r f g, add_monoid_hom.ext $ λ x,
    by rw [character_module.smul_apply, add_monoid_hom.add_apply, add_monoid_hom.add_apply,
      character_module.smul_apply, character_module.smul_apply],
  ..character_module.mul_action M}

instance character_module.module : module R (character_module M) :=
{ add_smul := λ a b f, add_monoid_hom.ext $ λ x, 
    by simp only [character_module.smul_apply, add_smul, add_monoid_hom.add_apply, map_add],
  zero_smul := λ f, add_monoid_hom.ext $ λ x, 
    by simp only [character_module.smul_apply, zero_smul, map_zero, add_monoid_hom.zero_apply],
  ..character_module.distrib_mul_action M}

namespace character_module

section map

variables {M N}

@[simps apply]
def map (L : M →ₗ[R] N) : character_module N →ₗ[R] character_module M :=
{ to_fun := λ f, f.comp L.to_add_monoid_hom,
  map_add' := λ f g, add_monoid_hom.ext $ λ x, by simp,
  map_smul' := λ r f, add_monoid_hom.ext $ λ x, by simp }

end map

lemma map_id : 
  map (linear_map.id : M →ₗ[R] M) = 
  (linear_map.id : character_module M →ₗ[R] character_module M) :=
linear_map.ext $ λ f, add_monoid_hom.ext $ λ x, by simp

section map

variables {M N N'}

lemma map_comp (L : M →ₗ[R] N) (L' : N →ₗ[R] N') :
  map (L'.comp L) = (map L).comp (map L') :=
linear_map.ext $ λ f, add_monoid_hom.ext $ λ x, by simp

lemma map_inj (L : M →ₗ[R] N) (hL : function.injective L) :
  function.surjective (map L) :=
λ g, ⟨begin 
  haveI : mono (AddCommGroup.of_hom L.to_add_monoid_hom) :=
    by rwa AddCommGroup.mono_iff_injective,
  exact injective.factor_thru (AddCommGroup.of_hom g) 
    (AddCommGroup.of_hom L.to_add_monoid_hom),
end, begin 
  ext x : 1,
  haveI : mono (AddCommGroup.of_hom L.to_add_monoid_hom) :=
    by rwa AddCommGroup.mono_iff_injective,
  rw [map_apply, add_monoid_hom.comp_apply],
  exact fun_like.congr_fun (injective.comp_factor_thru (AddCommGroup.of_hom g)
    (AddCommGroup.of_hom L.to_add_monoid_hom)) x,
end⟩

end map

def functor : (Module.{u} R)ᵒᵖ ⥤ Module.{u} R :=
{ obj := λ M, Module.of R $ character_module M.unop,
  map := λ M N L, map L.unop,
  map_id' := λ M, map_id M.unop,
  map_comp' := λ M N N' L L', map_comp L'.unop L.unop }

end character_module

end character_module