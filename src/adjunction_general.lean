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
def tensor_bimodule.smul_aux (s : S) : Y →ₗ[R] X →ₗ[R] Y ⊗[R] X :=
{ to_fun := λ y, 
  { to_fun := λ x, y ⊗ₜ (s • x),
    map_add' := λ x x', by rw [smul_add, tmul_add],
    map_smul' := λ r x, by rw [ring_hom.id_apply, smul_tmul', smul_tmul, 
      bimodule.smul_comm] },
  map_add' := λ y y', linear_map.ext $ λ x, by simp [linear_map.add_apply, 
    add_tmul],
  map_smul' := λ r y, linear_map.ext $ λ x, by simp [smul_tmul, tmul_smul] }

@[simps]
def tensor_bimodule.smul (s : S) : (Y ⊗[R] X) →ₗ[R] (Y ⊗[R] X) :=
tensor_product.lift $ tensor_bimodule.smul_aux _ _ _ _ s

instance tensor_product.bimodule.has_smul : has_smul S (Y ⊗[R] X) :=
{ smul := λ s, tensor_bimodule.smul R S X Y s }

section

variables {R S X Y}

lemma tensor_bimodule.smul_def (s : S) (z : Y ⊗[R] X) : 
  s • z = tensor_bimodule.smul _ _ _ _ s z := rfl


lemma tensor_bimodule.smul_tmul (s : S) (y : Y) (x : X) :
  s • (y ⊗ₜ x : _ ⊗[R] _) = y ⊗ₜ (s • x) := rfl

end

instance tensor_product.bimodule : module S (Y ⊗[R] X) :=
{ smul := (•),
  one_smul := λ z,
  begin 
    induction z using tensor_product.induction_on with _ _ a b ha hb,
    { rw [tensor_bimodule.smul_def, map_zero], },
    { rw [tensor_bimodule.smul_tmul, one_smul], },
    { rw [tensor_bimodule.smul_def] at ha hb ⊢,
      rw [map_add, ha, hb], },
  end,
  mul_smul := λ s s' z, 
  begin
    induction z using tensor_product.induction_on with y x a b ha hb,
    { simp only [tensor_bimodule.smul_def, map_zero], },
    { repeat { rw [tensor_bimodule.smul_tmul] },
      rw [mul_smul] },
    { repeat { rw [tensor_bimodule.smul_def] at ha hb ⊢ },
      rw [map_add, ha, hb, map_add, map_add], },
  end,
  smul_zero := λ s, by { rw [tensor_bimodule.smul_def, map_zero] },
  smul_add := λ _ _ _, by { simp only [tensor_bimodule.smul_def, map_add] },
  add_smul := λ s s' z, 
  begin 
    induction z using tensor_product.induction_on with y x a b ha hb,
    { simp only [tensor_bimodule.smul_def, map_zero, zero_add], },
    { repeat { rw [tensor_bimodule.smul_tmul] },
      rw [add_smul, tmul_add], },
    { repeat { rw [tensor_bimodule.smul_def] at ha hb ⊢, },
      simp only [map_add, ha, hb],
      abel, },
  end,
  zero_smul := λ z,
  begin
    induction z using tensor_product.induction_on with y x a b ha hb,
    { simp only [tensor_bimodule.smul_def, map_zero], },
    { repeat { rw [tensor_bimodule.smul_tmul] },
      rw [zero_smul, tmul_zero], },
    { repeat { rw [tensor_bimodule.smul_def] at ha hb ⊢, },
      simp only [map_add, ha, hb, add_zero], }, 
  end }

end tensor_bimodule

section bimodule_hom

variable [bimodule R S X]
variables (Z : Type v) [add_comm_group Z] [module S Z]

section

variables {R S X Z}

@[simps] def bimodule_hom.smul (r : R) (l : X →ₗ[S] Z) : X →ₗ[S] Z :=
{ to_fun := λ x, l (r • x),
  map_add' := λ _ _, by rw [smul_add, map_add],
  map_smul' := λ s x, by rw [bimodule.smul_comm, map_smul, 
    ring_hom.id_apply] }

end

instance bimodule_hom.has_smul : has_smul R (X →ₗ[S] Z) :=
{ smul := bimodule_hom.smul }

lemma bimodule_hom.smul_def (r : R) (l : X →ₗ[S] Z) :
  r • l = bimodule_hom.smul r l := rfl

instance bimodule_hom : module R (X →ₗ[S] Z) :=
{ smul := (•),
  one_smul := λ l, linear_map.ext $ λ x,
    by simp only [bimodule_hom.smul_def, bimodule_hom.smul_apply, one_smul],
  mul_smul := λ r r' l, linear_map.ext $ λ x,
  begin 
    simp only [bimodule_hom.smul_def, bimodule_hom.smul_apply, one_smul, mul_smul], 
    rw smul_comm,
  end,
  smul_zero := λ r, linear_map.ext $ λ x, 
    by simp only [bimodule_hom.smul_def, bimodule_hom.smul_apply, linear_map.zero_apply],
  smul_add := λ r l l', linear_map.ext $ λ x,
    by simp only [bimodule_hom.smul_def, bimodule_hom.smul_apply, linear_map.add_apply],
  add_smul := λ r r' l, linear_map.ext $ λ x,
    by simp only [bimodule_hom.smul_def, bimodule_hom.smul_apply, add_smul, map_add,
      linear_map.add_apply],
  zero_smul := λ l, linear_map.ext $ λ x,
  by simp only [bimodule_hom.smul_def, bimodule_hom.smul_apply, linear_map.zero_apply, 
    zero_smul, map_zero], }

end bimodule_hom

namespace Module

@[simps]
def tensor_functor [bimodule R S X] : Module.{v} R ⥤ Module.{v} S :=
{ obj := λ Y, Module.of S (Y ⊗[R] X),
  map := λ Y Y' l, 
  { to_fun := tensor_product.map l linear_map.id,
    map_add' := λ z z', by rw [map_add],
    map_smul' := λ s (z : Y ⊗[R] X),
    begin 
      induction z using tensor_product.induction_on with y x a b ha hb,
      { rw [smul_zero, map_zero, smul_zero], },
      { rw [tensor_bimodule.smul_tmul, map_tmul, linear_map.id_apply, map_tmul, ring_hom.id_apply, 
          linear_map.id_apply, tensor_bimodule.smul_tmul], },
      { rw [smul_add, map_add, ha, hb, map_add, smul_add], },
    end },
  map_id' := λ Y, linear_map.ext $ λ z,
  begin 
    simp only [linear_map.coe_mk, id_apply],
    erw [map_id, linear_map.id_apply],
  end,
  map_comp' := λ Y Y' Y'' l l', linear_map.ext $ λ z, 
  begin 
    simp only [linear_map.coe_mk, coe_comp, function.comp_app],
    induction z using tensor_product.induction_on with _ _ a b ha hb,
    { simp only [map_zero], },
    { simp only [tensor_product.map_tmul, linear_map.id_apply, category_theory.comp_apply] },
    { rw [map_add, ha, hb, map_add, map_add], }
  end }

@[simps]
def hom_functor [bimodule R S X] : Module.{v} S ⥤ Module R :=
{ obj := λ Z, Module.of R $ X →ₗ[S] Z,
  map := λ Z Z' (l : Z →ₗ[S] Z'), 
  { to_fun := l.comp,
    map_add' := λ z z', by rw linear_map.comp_add,
    map_smul' := λ r f, linear_map.ext $ λ x, rfl },
  map_id' := λ Z, 
    by { ext l x, simp only [linear_map.coe_mk, linear_map.comp_apply, id_apply] },
  map_comp' := λ Z Z' Z'' (l : Z →ₗ[S] Z') (l' : Z' →ₗ[S] Z''), 
    linear_map.ext $ λ (l'' : X →ₗ[S] Z), linear_map.ext $ λ x, by simp, }

end Module

namespace Module

variables (R' : Type u) (S' : Type u') [comm_ring R'] [comm_ring S']
variables (X' : Type v) [add_comm_group X'] [module R' X'] [module S' X'] [bimodule R' S' X']

namespace tensor_hom_adjunction

@[simps]
def hom_equiv.to_fun' {Y : Module.{v} R'} {Z : Module.{v} S'} (l : Y ⊗[R'] X' →ₗ[S'] Z) :
  (Y ⟶ (hom_functor R' S' X').obj Z) :=
{ to_fun := λ y, 
  { to_fun := λ x, l (y ⊗ₜ x),
    map_add' := λ x x', by rw [tmul_add, map_add],
    map_smul' := λ s x, by rw [ring_hom.id_apply, ←map_smul, tensor_bimodule.smul_tmul] },
  map_add' := λ y y', linear_map.ext $ λ x, by simp [add_tmul, map_add],
  map_smul' := λ r y, linear_map.ext $ λ x,by simp [bimodule_hom.smul_def, 
    bimodule_hom.smul_apply, smul_tmul], }

@[simps]
def hom_equiv.inv_fun' {Y : Module.{v} R'} {Z : Module.{v} S'} (l : Y →ₗ[R'] (X' →ₗ[S'] Z)) :
  ((tensor_functor R' S' X').obj Y ⟶ Z) :=
{ to_fun := (add_con_gen _).lift (free_add_monoid.lift $ show Y × X' → Z, from λ p, l p.1 p.2) $ 
    add_con.add_con_gen_le $ λ p p' (h : eqv R' Y X' p p'), 
      show (free_add_monoid.lift $ show Y × X' → Z, from λ p, l p.1 p.2) p 
        = (free_add_monoid.lift $ show Y × X' → Z, from λ p, l p.1 p.2) p',
      from match p, p', h with
      | _, _, (eqv.of_zero_left n) := by simp only [free_add_monoid.lift_eval_of, map_zero, 
        linear_map.zero_apply]
      | _, _, (eqv.of_zero_right m) := by simp only [free_add_monoid.lift_eval_of, map_zero]
      | _, _, (eqv.of_add_left m₁ m₂ n)  := by simp only [map_add, free_add_monoid.lift_eval_of, 
        linear_map.add_apply]
      | _, _, (eqv.of_add_right m n₁ n₂) := by simp only [map_add, free_add_monoid.lift_eval_of] 
      | _, _, (eqv.of_smul r m n) := by simp only [free_add_monoid.lift_eval_of, map_smul,
        bimodule_hom.smul_def, bimodule_hom.smul_apply]
      | _, _, (eqv.add_comm x y) := by simpa only [map_add, free_add_monoid.lift_eval_of] 
        using add_comm _ _ 
      end,
  map_add' := λ _ _, by rw map_add,
  map_smul' := λ s (z : Y ⊗[R'] X'), 
  begin 
    induction z using tensor_product.induction_on with y x a b ha hb,
    { rw [smul_zero, map_zero, smul_zero], },
    { rw [tensor_bimodule.smul_tmul, tmul, add_con.coe_mk', add_con.lift_coe, 
        free_add_monoid.lift_eval_of, ring_hom.id_apply, tmul, add_con.coe_mk', add_con.lift_coe,
        free_add_monoid.lift_eval_of],
      simp only [map_smul], },
    { rw [smul_add, map_add, ha, hb, map_add, smul_add], }
  end }


@[simps]
def hom_equiv (Y : Module.{v} R') (Z : Module.{v} S') :
  ((tensor_functor R' S' X').obj Y ⟶ Z) ≃ (Y ⟶ (hom_functor R' S' X').obj Z) :=
{ to_fun := hom_equiv.to_fun' R' S' X',
  inv_fun := hom_equiv.inv_fun' R' S' X',
  left_inv := λ l, linear_map.ext $ λ (p : Y ⊗[R'] X'), 
  begin 
    simp only [hom_equiv.to_fun'_apply_apply, hom_equiv.inv_fun'_apply],
    induction p using tensor_product.induction_on with y x a b ha hb,
    { rw [map_zero, map_zero], },
    { conv_lhs { rw [tmul, add_con.coe_mk', add_con.lift_coe, free_add_monoid.lift_eval_of] }, },
    { conv_lhs { rw [map_add, ha, hb, ←map_add], } }
  end,
  right_inv := λ (l : Y →ₗ[R'] (X'→ₗ[S'] Z)), linear_map.ext $ λ y, linear_map.ext $ λ x,
  begin 
    simp only [hom_equiv.to_fun'_apply_apply, hom_equiv.inv_fun'_apply],
    conv_lhs { rw [tmul, add_con.coe_mk', add_con.lift_coe, free_add_monoid.lift_eval_of] },
  end }

@[simps]
def unit : 𝟭 (Module R') ⟶ tensor_functor R' S' X' ⋙ hom_functor R' S' X' :=
{ app := λ Y, show Y →ₗ[R'] (X' →ₗ[S'] (Y ⊗[R'] X')), from 
  { to_fun := λ y, 
    { to_fun := λ x, y ⊗ₜ x,
      map_add' := λ x x', by rw tmul_add,
      map_smul' := λ s x, by rw [ring_hom.id_apply]; refl },
    map_add' := λ y y', linear_map.ext $ λ x, by simp only [linear_map.coe_mk, add_tmul, 
      linear_map.add_apply],
    map_smul' := λ r y, linear_map.ext $ λ x, by simp only [linear_map.coe_mk, linear_map.smul_apply,
      bimodule_hom.smul_def, bimodule_hom.smul_apply, ring_hom.id_apply, smul_tmul], },
  naturality' := λ Y Y' (l : Y →ₗ[R'] Y'), linear_map.ext $ λ (y : Y), linear_map.ext $ λ x,
  begin 
    simp only [category_theory.comp_apply, linear_map.coe_mk, category_theory.functor.id_map, 
      category_theory.functor.comp_map, hom_functor_map_apply, linear_map.comp_apply,
      tensor_functor_map_apply, map_tmul, linear_map.id_coe, id.def],
  end }

@[simps] def counit : hom_functor R' S' X' ⋙ tensor_functor R' S' X' ⟶ 𝟭 (Module S') :=
{ app := λ Z, show ((X' →ₗ[S'] Z) ⊗[R'] X') →ₗ[S'] Z, from 
  { to_fun := (add_con_gen _).lift (free_add_monoid.lift $ λ (p : (X' →ₗ[S'] ↥Z) × X'), p.1 p.2) $ 
    add_con.add_con_gen_le $ λ p p' (h : eqv R' (X' →ₗ[S'] Z) X' p p'), 
      show (free_add_monoid.lift $ λ (p : (X' →ₗ[S'] ↥Z) × X'), p.1 p.2) p = 
      (free_add_monoid.lift $ λ (p : (X' →ₗ[S'] ↥Z) × X'), p.1 p.2) p',
      from match p, p', h with
      | _, _, (eqv.of_zero_left n) := by simp only [free_add_monoid.lift_eval_of, map_zero, 
        linear_map.zero_apply]
      | _, _, (eqv.of_zero_right m) := by simp only [free_add_monoid.lift_eval_of, map_zero]
      | _, _, (eqv.of_add_left m₁ m₂ n)  := by simp only [map_add, free_add_monoid.lift_eval_of, 
        linear_map.add_apply]
      | _, _, (eqv.of_add_right m n₁ n₂) := by simp only [map_add, free_add_monoid.lift_eval_of] 
      | _, _, (eqv.of_smul r m n) := by simp only [free_add_monoid.lift_eval_of, map_smul,
        bimodule_hom.smul_def, bimodule_hom.smul_apply]
      | _, _, (eqv.add_comm x y) := by simpa only [map_add, free_add_monoid.lift_eval_of] 
        using add_comm _ _ 
      end,
    map_add' := λ p p', by rw map_add,
    map_smul' := 
    begin 
      rintros s p,
      induction p using tensor_product.induction_on with l x a b ha hb,
      { simp only [map_zero, smul_zero], },
      { rw [tensor_bimodule.smul_tmul, tmul, add_con.coe_mk', add_con.lift_coe, 
          free_add_monoid.lift_eval_of, ring_hom.id_apply, tmul, add_con.coe_mk', add_con.lift_coe, 
          free_add_monoid.lift_eval_of, linear_map.map_smul], },
      { rw [smul_add, map_add, ha, hb, map_add, smul_add] }
    end },
  naturality' := λ Z Z' (l : Z →ₗ[S'] Z'), linear_map.ext $ λ (p : (X' →ₗ[S'] Z) ⊗[R'] X'), 
  begin 
    induction p using tensor_product.induction_on with l' x a b ha hb,
    { simp only [map_zero] },
    { simp only [category_theory.comp_apply, linear_map.coe_mk, category_theory.functor.comp_map,
        hom_functor_map_apply, tensor_functor_map_apply, tensor_product.map_tmul,
        category_theory.functor.id_map, linear_map.id_apply],
      simp only [tmul, add_con.coe_mk', add_con.lift_coe, free_add_monoid.lift_eval_of, 
        linear_map.comp_apply], },
    { rw [map_add, ha, hb, map_add], },
  end }

lemma hom_equiv_unit (Y : Module.{v} R') (Z : Module.{v} S') (f) : 
  hom_equiv R' S' X' Y Z f =
  (unit R' S' X').app Y ≫ (hom_functor R' S' X').map f :=
linear_map.ext $ λ y, linear_map.ext $ λ x, rfl

lemma hom_equiv_counit (Y : Module.{v} R') (Z : Module.{v} S') (g) : 
  (hom_equiv R' S' X' Y Z).symm g =
  (tensor_functor _ _ _).map g ≫ (counit R' S' X').app Z :=
linear_map.ext $ λ z,
begin 
  induction z using tensor_product.induction_on with y x a b ha hb,
  { simp only [map_zero] },
  { conv_lhs { rw [hom_equiv_symm_apply, hom_equiv.inv_fun'_apply, tmul, add_con.coe_mk', 
      add_con.lift_coe, free_add_monoid.lift_eval_of] },
    conv_rhs { rw [category_theory.comp_apply, tensor_functor_map_apply, tensor_product.map_tmul,
      linear_map.id_apply, counit_app_apply, tmul, add_con.coe_mk', add_con.lift_coe, 
      free_add_monoid.lift_eval_of] }, },
  { rw [map_add, ha, hb, map_add] },
end

end tensor_hom_adjunction

@[simps]
def tensor_hom_adjunction : (tensor_functor R' S' X') ⊣ (hom_functor R' S' X') :=
{ hom_equiv := tensor_hom_adjunction.hom_equiv _ _ _,
  unit := tensor_hom_adjunction.unit _ _ _,
  counit := tensor_hom_adjunction.counit _ _ _,
  hom_equiv_unit' := tensor_hom_adjunction.hom_equiv_unit _ _ _,
  hom_equiv_counit' := tensor_hom_adjunction.hom_equiv_counit _ _ _ }

end Module

namespace tensor_product

variables (R' : Type u) [comm_ring R']
variables {M N : Type v} [add_comm_group M] [add_comm_group N]
variables [module R' M] [module R' N]

@[simps]
def to_add_comm_group {C : Type v} [add_comm_group C]
  (b : M →+ (N →+ C)) (hb : ∀ (r : R') (m : M) (n : N), b (r • m) n = b m (r • n)) :
  (M ⊗[R'] N) →+ C :=
(((@Module.tensor_hom_adjunction R' ℤ _ _ N _ _ _ (bimodule.int _)).hom_equiv 
  (Module.of R' M) (Module.of _ C)).symm 
{ to_fun := λ (m : M), add_monoid_hom.to_int_linear_map $ b m,
  map_add' := λ (m m' : M), by rw [map_add]; refl,
  map_smul' := λ r (m : M), linear_map.ext $ λ n, 
  by simpa only [add_monoid_hom.coe_to_int_linear_map, ring_hom.id_apply, hb] }).to_add_monoid_hom

lemma to_add_comm_group.apply_tmul {C : Type v} [add_comm_group C]
  (b : M →+ (N →+ C)) (hb : ∀ (r : R') (m : M) (n : N), b (r • m) n = b m (r • n))
  (m : M) (n : N) : to_add_comm_group R' b hb (m ⊗ₜ n) = b m n :=
by rw [to_add_comm_group_apply, tmul, add_con.coe_mk', add_con.lift_coe,
    free_add_monoid.lift_eval_of]

lemma to_add_comm_group.uniq {C : Type v} [add_comm_group C]
  (b : M →+ (N →+ C)) (hb : ∀ (r : R') (m : M) (n : N), b (r • m) n = b m (r • n))
  (l : (M ⊗[R'] N) →+ C) (hl : ∀ ⦃m : M⦄ ⦃n : N⦄,  l (m ⊗ₜ n) = b m n) :
  to_add_comm_group R' b hb = l := add_monoid_hom.ext $ λ z,
begin 
  induction z using tensor_product.induction_on with m n x y hx hy,
  { simp only [map_zero] },
  { rw [to_add_comm_group.apply_tmul, hl], },
  { rw [map_add, hx, hy, map_add] },
end

@[reducible]
def to_add_comm_group' {C : Type v} [add_comm_group C]
  (b : M × N → C) 
  (hN0 : ∀ (n : N), b (0, n) = 0)
  (hM0 : ∀ (m : M), b (m, 0) = 0)
  (hMadd : ∀ (n : N) (m m' : M), b (m + m', n) = b (m, n) + b (m', n))
  (hNadd : ∀ (m : M) (n n' : N), b (m, n + n') = b (m, n) + b (m, n'))
  (hb : ∀ (r : R') (m : M) (n : N), b ((r • m), n) = b (m, (r • n))) :
  (M ⊗[R'] N) →+ C :=
to_add_comm_group R' 
{ to_fun := λ m, 
  { to_fun := λ n, b (m, n),
    map_zero' := hM0 _,
    map_add' := hNadd _ },
  map_zero' := add_monoid_hom.ext $ λ n, show b (0, n) = 0, from hN0 _,
  map_add' := λ m m', add_monoid_hom.ext $ λ n, show b (m + m', n) = b (m, n) + b (m', n), 
    from hMadd _ _ _ } $ λ r m n,
show b (r • m, n) = b (m, r • n), from hb _ _ _

lemma to_add_comm_group'.apply_tmul {C : Type v} [add_comm_group C]
  (b : M × N → C) 
  (hN0 : ∀ (n : N), b (0, n) = 0)
  (hM0 : ∀ (m : M), b (m, 0) = 0)
  (hMadd : ∀ (n : N) (m m' : M), b (m + m', n) = b (m, n) + b (m', n))
  (hNadd : ∀ (m : M) (n n' : N), b (m, n + n') = b (m, n) + b (m, n'))
  (hb : ∀ (r : R') (m : M) (n : N), b ((r • m), n) = b (m, (r • n)))
  (m : M) (n : N) : to_add_comm_group' R' b hN0 hM0 hMadd hNadd hb (m ⊗ₜ n) = b (m, n) :=
by rw [to_add_comm_group.apply_tmul]; refl

open_locale big_operators

lemma exists_rep (z : M ⊗[R'] N) : 
  ∃ (ms : ℕ → M) (ns : ℕ → N) (s : finset ℕ),
  z = ∑ i in s, ms i ⊗ₜ ns i :=
sorry

end tensor_product