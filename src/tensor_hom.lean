import linear_algebra.tensor_product
import algebra.category.Module.basic

universes u v

variables {R S : Type u} [comm_ring R] [comm_ring S]

open_locale tensor_product

namespace tensor_product

section

variables {M' M N : Type v} [add_comm_group M'] [module R M'] 
variables [add_comm_group M] [module R M]
variables [add_comm_group N]

/--
This probably doesn't follow from universal propoerty of tensor product
-/
def lift_add_monoid_hom (b : M' × M →+ N)
  (hb10 : ∀ (m'1 m'2 : M') (m : M), b (m'1 + m'2, m) = b (m'1, m) + b (m'2, m))
  (hb11 : ∀ (m : M), b (0, m) = 0)
  (hb20 : ∀ (m' : M') (m1 m2 : M), b (m', m1 + m2) = b (m', m1) + b (m', m2))
  (hb21 : ∀ (m' : M'), b (m', 0) = 0)
  (hb3 : ∀ (r : R) (m' : M') (m : M), b (r • m', m) = b (m', r • m)) :
  M' ⊗[R] M →+ N :=
(add_con_gen (tensor_product.eqv _ _ _)).lift 
  (free_add_monoid.lift b) $ add_con.add_con_gen_le $ λ x y h,
  match x,y, h with
  | _, _, (tensor_product.eqv.of_zero_left m) := (add_con.ker_rel _).2 $ 
    by rw [free_add_monoid.lift_apply, free_add_monoid.to_list_of, list.map, 
      list.sum_cons, list.map_nil, list.sum_nil, add_zero, free_add_monoid.lift_apply,
      free_add_monoid.to_list_zero, list.map_nil, list.sum_nil, hb11]
  | _, _, (tensor_product.eqv.of_zero_right m) := (add_con.ker_rel _).2 $ 
    by rw [free_add_monoid.lift_apply, free_add_monoid.to_list_of, list.map, 
      list.sum_cons, list.map_nil, list.sum_nil, add_zero, free_add_monoid.lift_apply,
      free_add_monoid.to_list_zero, list.map_nil, list.sum_nil, hb21]
  | _, _, (tensor_product.eqv.of_add_left m₁ m₂ n)  := (add_con.ker_rel _).2 $ 
    by rw [map_add, free_add_monoid.lift_apply, free_add_monoid.lift_apply,
      free_add_monoid.to_list_of, free_add_monoid.to_list_of, list.map, list.sum_cons,
      list.map_nil, list.sum_nil, list.map, list.sum_cons, list.map_nil, list.sum_nil,
      add_zero, add_zero, free_add_monoid.lift_apply, free_add_monoid.to_list_of,
      list.map, list.sum_cons, list.map_nil, list.sum_nil, add_zero, hb10]
  | _, _, (tensor_product.eqv.of_add_right m n₁ n₂) := (add_con.ker_rel _).2 $ 
    by rw [map_add, free_add_monoid.lift_apply, free_add_monoid.lift_apply,
      free_add_monoid.to_list_of, free_add_monoid.to_list_of, list.map, list.sum_cons,
      list.map_nil, list.sum_nil, list.map, list.sum_cons, list.map_nil, list.sum_nil,
      add_zero, add_zero, free_add_monoid.lift_apply, free_add_monoid.to_list_of,
      list.map, list.sum_cons, list.map_nil, list.sum_nil, add_zero, hb20]
  | _, _, (tensor_product.eqv.of_smul s m n)        := (add_con.ker_rel _).2 $ 
    by rw [free_add_monoid.lift_apply, free_add_monoid.lift_apply, free_add_monoid.to_list_of,
      free_add_monoid.to_list_of, list.map, list.map_nil, list.sum_cons, list.sum_nil, add_zero,
      list.map, list.map_nil, list.sum_cons, list.sum_nil, add_zero, hb3]
  | _, _, (tensor_product.eqv.add_comm x y)         := (add_con.ker_rel _).2 $ 
    by rw [free_add_monoid.lift_apply, free_add_monoid.lift_apply, 
      free_add_monoid.to_list_add, free_add_monoid.to_list_add, list.map_append,
      list.map_append, list.sum_append, list.sum_append, add_comm]
  end

end

section

variables {R} (M : Module.{v} R)

@[simps]
def left_functor : Module.{v} R ⥤ Module.{v} R :=
{ obj := λ N, Module.of R $ N ⊗[R] M,
  map := λ N N' f, Module.of_hom $ tensor_product.map f linear_map.id,
  map_id' := λ X, linear_map.ext $ λ x, 
  begin 
    induction x using tensor_product.induction_on with _ _ a b ha hb,
    { simp },
    { erw [tensor_product.map_tmul], },
    { rw [map_add, ha, hb, map_add], },
  end,
  map_comp' := λ X Y Z f g, linear_map.ext $ λ x, 
  begin 
    induction x using tensor_product.induction_on with _ _ a b ha hb,
    { simp },
    { erw [tensor_product.map_tmul], },
    { rw [map_add, map_add, ha, hb], },
  end }

end

end tensor_product