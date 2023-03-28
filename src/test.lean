-- import category_theory.functor.left_derived
-- import category_theory.monoidal.tor
-- import category_theory.monoidal.braided

import algebra.category.Module.basic
import linear_algebra.direct_sum.finsupp

lemma linear_map.map_ite {R : Type*} [comm_ring R] (L M N : Type*)
  [add_comm_monoid L] [add_comm_monoid M] [add_comm_monoid N]
  [module R L] [module R M] [module R N] (f f' : L →ₗ[R] M) (g : M →ₗ[R] N) 
  (p : Prop) [decidable p] (x) :
  g ((if p then f else f') x) = if p then g (f x) else g (f' x) :=
begin 
  split_ifs;
  refl,
end

lemma linear_map.comp_ite {R : Type*} [comm_ring R] (L M N : Type*)
  [add_comm_monoid L] [add_comm_monoid M] [add_comm_monoid N]
  [module R L] [module R M] [module R N] (f f' : L →ₗ[R] M) (g : M →ₗ[R] N) 
  (p : Prop) [decidable p] :
  g.comp (if p then f else f') = if p then g.comp f else g.comp f' :=
begin 
  split_ifs;
  refl,
end

lemma linear_map.map_dite {R : Type*} [comm_ring R] (L M N : Type*)
  [add_comm_monoid L] [add_comm_monoid M] [add_comm_monoid N]
  [module R L] [module R M] [module R N] (g : M →ₗ[R] N) 
  (p : Prop) [decidable p]
  (f : p → (L →ₗ[R] M)) (f' : ¬ p → (L →ₗ[R] M)) (x) :
  g ((if H : p
  then f H
  else f' H) x) = if H : p then g (f H x) else g (f' H x) :=
begin 
  split_ifs;
  refl,
end

lemma linear_map.comp_sum {R : Type*} [comm_ring R] (L M N : Type*)
  [add_comm_monoid L] [add_comm_monoid M] [add_comm_monoid N]
  [module R L] [module R M] [module R N] (g : M →ₗ[R] N) {ι : Type*} (s : finset ι)
  (f : ι → (L →ₗ[R] M)) : g.comp (s.sum f) = s.sum (λ x, g.comp $ f x) :=
begin 
  classical,
  induction s using finset.induction_on with _ _ h ih,
  { rw [finset.sum_empty, linear_map.comp_zero, finset.sum_empty], },
  { rw [finset.sum_insert h, linear_map.comp_add, finset.sum_insert h, ih], },
end

lemma linear_map.ite_apply {R : Type*} [comm_ring R] (L M : Type*)
  [add_comm_monoid L] [add_comm_monoid M]
  [module R L] [module R M] 
  (p : Prop) [decidable p]
  (f : (L →ₗ[R] M)) (f' : (L →ₗ[R] M)) (x) :
  (if p
  then f
  else f') x = if p then f x else f' x :=
begin 
  split_ifs;
  refl,
end

lemma linear_map.dite_apply {R : Type*} [comm_ring R] (L M : Type*)
  [add_comm_monoid L] [add_comm_monoid M]
  [module R L] [module R M] 
  (p : Prop) [decidable p]
  (f : p → (L →ₗ[R] M)) (f' : ¬ p → (L →ₗ[R] M)) (x) :
  (if H : p
  then f H
  else f' H) x = if H : p then f H x else f' H x :=
begin 
  split_ifs;
  refl,
end

open_locale direct_sum

lemma direct_sum.dite_apply (R : Type*) [comm_ring R]
  (p : Prop) [decidable p] 
  {ι : Type*}  (M : (ι → Type*))  [∀ i , add_comm_monoid (M i)] [∀ i , module R (M i)]
  (x : p → ⨁ i, M i)
  (x' : ¬ p → ⨁ i, M i) (y) :
  (if H : p then x H else x' H) y = 
  if H : p then x H y else x' H y :=
begin 
  split_ifs;
  refl,
end

lemma direct_sum.apply_dite (R : Type*) [comm_ring R]
  (p : Prop) [decidable p] 
  {ι : Type*}  (M : (ι → Type*))  [∀ i , add_comm_monoid (M i)] [∀ i , module R (M i)]
  (x : ⨁ i, M i) (y : p → ι) (y' : ¬ p → ι) :
  x (if H : p then y H else y' H) = 
  (if H : p then x _ else x _) :=
begin 
  split_ifs;
  refl,
end

open_locale big_operators

lemma finset.sum_subsingleton {ι M : Type*} [add_comm_monoid M]
  (s : set ι) (hs : s.subsingleton) [decidable s.nonempty] (f : ι → M) :
  ∑ i in hs.finite.to_finset, f i = 
  if H : s.nonempty then f H.some else 0 :=
begin 
  have s_eq : s = if H : s.nonempty then {H.some} else ∅,
  { split_ifs with H, 
    { ext1, simp only [set.mem_singleton_iff],
      split,
      { intros h, refine hs h H.some_spec, },
      { intros h, rw h, exact H.some_spec, }, },
    { rwa set.not_nonempty_iff_eq_empty at H, }, },
  split_ifs with H,
  { rw dif_pos H at s_eq,
    transitivity ∑ i in {H.some}, f i,
    { refine finset.sum_congr _ (λ _ _, rfl),
      ext, simp only [set.finite.mem_to_finset, finset.mem_singleton],
      rw ← set.mem_singleton_iff,
      convert iff.rfl, exact s_eq.symm, },
  rw finset.sum_singleton },
  { rw set.not_nonempty_iff_eq_empty at H,
    transitivity ∑ i in ∅, f i,
    { refine finset.sum_congr _ (λ _ _, rfl),
      simpa only [set.finite_to_finset_eq_empty_iff], },
    rw finset.sum_empty, },
end

-- noncomputable theory

-- open category_theory
-- open category_theory.limits

-- universes v u

-- namespace category_theory

-- section

-- variables {C : Type u} [category.{v} C] {D : Type*} [category D]

-- -- Importing `category_theory.abelian.projective` and assuming
-- -- `[abelian C] [enough_projectives C] [abelian D]` suffices to acquire all the following:
-- variables [preadditive C] [has_zero_object C] [has_equalizers C]
--   [has_images C] [has_projective_resolutions C]
-- variables [preadditive D] [has_equalizers D] [has_cokernels D]
--   [has_images D] [has_image_maps D]

-- @[simps]
-- def nat_iso.left_derived {F G : C ⥤ D} [F.additive] [G.additive] (α : F ≅ G) (n : ℕ) :
--   F.left_derived n ≅ G.left_derived n :=
-- { hom := α.hom.left_derived n,
--   inv := α.inv.left_derived n,
--   hom_inv_id' := by rw [←nat_trans.left_derived_comp, iso.hom_inv_id, nat_trans.left_derived_id],
--   inv_hom_id' := by rw [←nat_trans.left_derived_comp, iso.inv_hom_id, nat_trans.left_derived_id], }

-- end

-- section

-- variables {C : Type*} [category C] 
--   [monoidal_category C] [symmetric_category C] [preadditive C] 
--   [monoidal_preadditive C]
--   [has_zero_object C] [has_equalizers C] [has_cokernels C] [has_images C] [has_image_maps C]
--   [has_projective_resolutions C]

-- /--

-- `(Tor C n).obj X` is left deriving the functor `X ⊗ -`, i.e. `((Tor C n).obj X).obj Y` is
-- - take a projective resolution of `P_* → Y` and apply `X ⊗ -` to yield
-- ```
-- X ⊗ P_n → X ⊗ P_{n-1} → ⋯
-- ```
-- and calculate homology
-- -/
-- def Tor.is_balanced (n : ℕ) (X Y) : ((Tor C n).obj X).obj Y ⟶ ((Tor' C n).obj Y).obj X :=
-- show ((monoidal_category.tensor_left X).left_derived n).obj Y ⟶ 
--   ((monoidal_category.tensor_right X).left_derived n).obj Y,
-- from 
-- (nat_trans.left_derived 
-- ({ app := λ Y, (β_ X Y).hom,
--   naturality' := λ Y Y' f, by simp } : 
--   monoidal_category.tensor_left X ⟶ monoidal_category.tensor_right X) n).app Y

-- #check nat_iso.hom_app_is_iso

-- end

-- end category_theory