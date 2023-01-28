import algebra.direct_limit
import linear_algebra.tensor_product

open_locale tensor_product

universes u v w

variables {R : Type u} [comm_ring R]
variables {ι : Type v}
variables [decidable_eq ι] [preorder ι]
variables (G : ι → Type w)

namespace module

variables [Π i, add_comm_group (G i)] [Π i, module R (G i)]

variables {G} (f : Π i j, i ≤ j → G i →ₗ[R] G j)

variables (M : Type w) [add_comm_group M] [module R M]

@[reducible]
def direct_limit_of_tensor_product_to_tensor_product_with_direct_limit : 
  direct_limit (λ i, G i ⊗[R] M) 
    (λ i j hij, tensor_product.map (f _ _ hij) (linear_map.id)) →ₗ[R] (direct_limit G f) ⊗[R] M := 
direct_limit.lift _ _ _ _ (λ i, tensor_product.map (direct_limit.of _ _ _ _ _) linear_map.id) $ 
λ i j hij z, 
begin 
  induction z using tensor_product.induction_on with g m x y hx hy,
  { simp only [map_zero] },
  { simp only [tensor_product.map_tmul, direct_limit.of_f, linear_map.id_apply], },
  { rw [map_add, map_add, hx, hy, map_add] },
end

@[reducible]
def tensor_product_with_direct_limit_to_direct_limit_of_tensor_product :
(direct_limit G f) ⊗[R] M →ₗ[R] direct_limit (λ i, G i ⊗[R] M) 
  (λ i j hij, tensor_product.map (f _ _ hij) (linear_map.id)) :=
tensor_product.lift $ direct_limit.lift _ _ _ _ (λ i, 
{ to_fun := λ g, 
  { to_fun := λ m, direct_limit.of R ι (λ i, G i ⊗[R] M) 
        (λ i j hij, tensor_product.map (f _ _ hij) (linear_map.id)) i $ g ⊗ₜ m,
    map_add' := λ m m', by rw [tensor_product.tmul_add, map_add],
    map_smul' := λ r m, by rw [←tensor_product.smul_tmul, ←tensor_product.smul_tmul', map_smul,
      ring_hom.id_apply] },
  map_add' := λ g g', 
  begin 
    ext1 m,
    simp only [linear_map.coe_mk, linear_map.add_apply, tensor_product.add_tmul, map_add],
  end,
  map_smul' := λ r g,
  begin
    ext1 m,
    simp only [linear_map.coe_mk, ring_hom.id_apply, linear_map.smul_apply, 
      ←tensor_product.smul_tmul', map_smul],
  end }) $ λ i j hij g, linear_map.ext $ λ m, 
  show direct_limit.of R ι (λ (i : ι), G i ⊗[R] M)
    (λ i j hij, tensor_product.map (f i j hij) linear_map.id) j
    ((f i j hij) g ⊗ₜ[R] m) =
  (direct_limit.of R ι (λ (i : ι), G i ⊗[R] M)
    (λ i j hij, tensor_product.map (f i j hij) linear_map.id) i)
    (g ⊗ₜ[R] m), from
by rw [show (f i j hij) g ⊗ₜ[R] m = (tensor_product.map (f i j hij) linear_map.id) (g ⊗ₜ[R] m), 
  from tensor_product.map_tmul (f i j hij) linear_map.id g m, direct_limit.of_f]

variables [is_directed ι (≤)] [nonempty ι]

lemma direct_limit_of_tensor_product_iso_tensor_product_with_direct_limit.left_inv :
  function.left_inverse 
    (tensor_product_with_direct_limit_to_direct_limit_of_tensor_product f M)
    (direct_limit_of_tensor_product_to_tensor_product_with_direct_limit f M) :=
begin 
  intros z,
  induction z using module.direct_limit.induction_on with i z,
  induction z using tensor_product.induction_on with g m x y hx hy,
  { simp only [map_zero] },
  { rw [direct_limit.lift_of, tensor_product.map_tmul, linear_map.id_apply, 
      tensor_product.lift.tmul, direct_limit.lift_of],
    refl, },
  { simp only [map_add, hx, hy] },
end

lemma direct_limit_of_tensor_product_iso_tensor_product_with_direct_limit.right_inv :
  function.right_inverse 
    (tensor_product_with_direct_limit_to_direct_limit_of_tensor_product f M)
    (direct_limit_of_tensor_product_to_tensor_product_with_direct_limit f M) :=
begin 
  intros z,
  induction z using tensor_product.induction_on with d m x y hx hy,
  { simp only [map_zero] },
  { induction d using module.direct_limit.induction_on with i g,
    rw [tensor_product.lift.tmul, direct_limit.lift_of],
    simp only [linear_map.coe_mk],
    rw [direct_limit.lift_of],
    refl, },
  { simp only [map_add, hx, hy] },
end

@[simps]
def direct_limit_of_tensor_product_iso_tensor_product_with_direct_limit : 
  direct_limit (λ i, G i ⊗[R] M) 
    (λ i j hij, tensor_product.map (f _ _ hij) (linear_map.id)) ≃ₗ[R] (direct_limit G f) ⊗[R] M := 
{ inv_fun := tensor_product_with_direct_limit_to_direct_limit_of_tensor_product f M,
  left_inv := direct_limit_of_tensor_product_iso_tensor_product_with_direct_limit.left_inv f M,
  right_inv := direct_limit_of_tensor_product_iso_tensor_product_with_direct_limit.right_inv f M,
  ..direct_limit_of_tensor_product_to_tensor_product_with_direct_limit f M }

universes u₁

variables {P : Type u₁} [add_comm_group P] [module R P] (g : Π i, G i →ₗ[R] P)
variables (Hg₁ : ∀ i j hij x, g j (f i j hij x) = g i x)
variables (Hg₂ : ∀ i, function.injective $ g i)
include Hg₁ Hg₂

variables (R ι G f)

lemma lift_inj : 
  function.injective $ direct_limit.lift R ι G f g Hg₁ :=
begin 
  simp_rw [←linear_map.ker_eq_bot, submodule.eq_bot_iff, linear_map.mem_ker] at Hg₂ ⊢,
  intros z hz,
  induction z using module.direct_limit.induction_on with i gi,
  rw direct_limit.lift_of at hz,
  specialize Hg₂ i gi hz,
  rw Hg₂,
  simp only [map_zero],
end

end module