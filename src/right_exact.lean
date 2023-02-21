import linear_algebra.tensor_product
import algebra.category.Module.monoidal
import algebra.homology.exact

import .adjunction_general

universes u v

open category_theory
open_locale tensor_product zero_object

namespace tensor_product

variables (R : Type u) [comm_ring R]
variables (M : Type v) [add_comm_group M] [module R M]
variables (A B C : Module.{v} R)

variables (fAB : A ⟶ B) (fBC : B ⟶ C)
variables (e0A : exact (0 : (0 : Module.{v} R) ⟶ _) fAB) 
variables (eAB : exact fAB fBC) (eC0 : exact fBC (0 : _ ⟶ (0 : Module.{v} R)))

-- include fAB fBC e0A eAB eC0

/-
```
0 -----> A ---fAB---> B ---fBC---> C ----> 0
``` 
is exact
then
```
A ⊗ M --> B ⊗ M ---> C ⊗ M ----> 0
```
is exact
-/

section

include fBC eC0

lemma right_exact.at3 :
  exact 
    (by exact map fBC linear_map.id : Module.of R (B ⊗[R] M) ⟶ Module.of R (C ⊗[R] M))
    (0 : _ ⟶ (0 : Module.{v} R)) :=
begin 
  rw ←epi_iff_exact_zero_right,
  haveI : bimodule R R M,
  { refine ⟨λ r r' m, _⟩,
    rw [←mul_smul, mul_comm, mul_smul] },
  haveI : epi fBC,
  { rw ←epi_iff_exact_zero_right at eC0,
    exact eC0 },
  haveI epi0 : epi ((Module.tensor_functor R R M).map fBC),
  { apply_instance },
  rw Module.epi_iff_surjective at epi0 ⊢,
  exact epi0,
end

lemma right_exact.surj :
  function.surjective fBC :=
begin 
  haveI e : epi fBC := by rwa ←epi_iff_exact_zero_right at eC0,
  rwa Module.epi_iff_surjective at e,
end

end

@[reducible] noncomputable def β_aux' : C → B :=
λ c, (@@right_exact.surj R _ B C fBC eC0 c).some

local notation `β_aux` := @@β_aux' R _ B C fBC eC0 

lemma β_aux_spec (z) : 
  fBC (β_aux z) = z := 
(@@right_exact.surj R _ B C fBC eC0 z).some_spec

section

include eAB

lemma right_exact.range_subset_ker :
  (map fAB linear_map.id : A ⊗[R] M →ₗ[R] B ⊗[R] M).range ≤ 
  (map fBC linear_map.id : B ⊗[R] M →ₗ[R] C ⊗[R] M).ker :=
begin 
  rintros _ ⟨z, rfl⟩,
  induction z using tensor_product.induction_on with a m x y hx hy,
  { simp only [map_zero, linear_map.mem_ker], }, 
  { simp only [map_tmul, linear_map.id_apply],
    have mem1 : fAB a ∈ fAB.range := ⟨_, rfl⟩,
    rw Module.exact_iff at eAB,
    rw [eAB, linear_map.mem_ker] at mem1,
    rw [linear_map.mem_ker, map_tmul, mem1, zero_tmul], },
  { simp only [map_add],
    exact submodule.add_mem _ hx hy, },
end

end

namespace right_exact.ker_subset_range

local notation `quotient_space` := (B ⊗[R] M) ⧸ (map fAB linear_map.id : A ⊗[R] M →ₗ[R] B ⊗[R] M).range

@[reducible]
def π' : B ⊗[R] M →ₗ[R] quotient_space :=
submodule.mkq _

local notation `π` := π' R M A B fAB

@[reducible]
def α' : quotient_space →ₗ[R] C ⊗[R] M :=
submodule.liftq _ (map fBC linear_map.id) $ λ x hx, right_exact.range_subset_ker R M A B C fAB fBC eAB hx

local notation `α` := @α' R _ M _ _ A B C fAB fBC eAB

section

include eAB

lemma β_wd ⦃b b' : B⦄ (h : fBC b = fBC b') (m : M) :
  π (b ⊗ₜ m) = π (b' ⊗ₜ m) :=
(submodule.quotient.eq' _).mpr 
begin
  rw [add_comm, ←sub_eq_add_neg, ←sub_tmul],
  rw [←sub_eq_zero, ←map_sub] at h,
  have mem1 : b' - b ∈ linear_map.range fAB,
  { rw Module.exact_iff at eAB, 
    rw ←neg_sub,
    refine submodule.neg_mem _ _, 
    rwa eAB, },
  rcases mem1 with ⟨a, ha⟩,
  rw ←ha,
  rw linear_map.mem_range,
  refine ⟨a ⊗ₜ m, _⟩,
  rw [map_tmul, linear_map.id_apply],
end

@[reducible] noncomputable def β' : C ⊗[R] M →ₗ[R] quotient_space :=
tensor_product.lift 
{ to_fun := λ c, 
  { to_fun := λ m, π $ β_aux c ⊗ₜ m,
    map_add' := λ m m', by rw [←map_add, ←tmul_add],
    map_smul' := λ r m, by rw [ring_hom.id_apply, ←π .map_smul, ←smul_tmul, ←smul_tmul'] },
  map_add' := λ c c', linear_map.ext $ λ m, 
  begin 
    simp only [linear_map.coe_mk, linear_map.add_apply],
    rw [←map_add, ←add_tmul],
    apply β_wd R M _ _ _ _ _ eAB,
    simp only [map_add, β_aux_spec],
  end,
  map_smul' := λ r c', linear_map.ext $ λ m, 
  begin 
    simp only [linear_map.coe_mk, ring_hom.id_apply, linear_map.smul_apply, ←π .map_smul],
    apply β_wd R M _ _ _ _ _ eAB,
    rw [linear_map.map_smul, β_aux_spec, β_aux_spec],
  end }

end

local notation `β` := @β' R _ M _ _ A B C fAB fBC eAB eC0

lemma αβ : α .comp β  = linear_map.id :=
linear_map.ext $ λ z, begin 
  rw [linear_map.id_apply, linear_map.comp_apply],
  induction z using tensor_product.induction_on with c m z z' hz hz',
  { simp only [map_zero], },
  { erw [lift.tmul, linear_map.comp_apply],
    simpa only [linear_map.id_apply, β_aux_spec], },
  { rw [map_add, map_add, hz, hz'], },
end

lemma βα : β .comp α = linear_map.id :=
linear_map.ext $ λ z, 
begin 
  induction z using quotient.induction_on,
  simp only [linear_map.comp_apply, linear_map.id_apply],
  erw submodule.liftq_apply,
  induction z using tensor_product.induction_on with c m x y hx hy,
  { simpa only [map_zero], },
  { simp only [map_tmul, lift.tmul, linear_map.coe_mk, linear_map.id_apply],
    apply β_wd R M _ _ _ _ _ eAB,
    rw β_aux_spec, },
  { simpa only [map_add, hx, hy], },
end

section

include eAB eC0

lemma result (z : B ⊗[R] M) (hz : z ∈ (map fBC linear_map.id : B ⊗[R] M →ₗ[R] C ⊗[R] M).ker) :
  z ∈ (map fAB linear_map.id : A ⊗[R] M →ₗ[R] B ⊗[R] M).range :=
begin 
  have EQ : α (π z) = 0,
  { erw submodule.liftq_apply, exact hz },
  apply_fun β at EQ,
  rw [←linear_map.comp_apply, βα, linear_map.id_apply, map_zero] at EQ,
  erw submodule.quotient.mk_eq_zero at EQ,
  exact EQ,
end

end

end right_exact.ker_subset_range

include eAB eC0

lemma right_exact.ker_subset_range :
  (map fBC linear_map.id : B ⊗[R] M →ₗ[R] C ⊗[R] M).ker ≤
  (map fAB linear_map.id : A ⊗[R] M →ₗ[R] B ⊗[R] M).range :=
@right_exact.ker_subset_range.result R _ M _ _ A B C fAB fBC eAB eC0

lemma right_exact :
  exact 
    (by exact map fAB linear_map.id : Module.of R (A ⊗[R] M) ⟶ Module.of R (B ⊗[R] M)) 
    (by exact map fBC linear_map.id : Module.of R (B ⊗[R] M) ⟶ Module.of R (C ⊗[R] M)) ∧
  exact 
    (by exact map fBC linear_map.id : Module.of R (B ⊗[R] M) ⟶ Module.of R (C ⊗[R] M))
    (0 : _ ⟶ (0 : Module.{v} R)) :=
⟨begin 
  rw Module.exact_iff,
  refine le_antisymm _ _,
  { intros x hx,
    exact @@right_exact.range_subset_ker R _ M _ _ A B C fAB fBC eAB hx, },
  { intros x hx,
    exact @@right_exact.ker_subset_range R _ M _ _ A B C fAB fBC eAB eC0 hx, },
end, by exactI @@right_exact.at3 R _ M _ _ B C fBC eC0⟩

end tensor_product
