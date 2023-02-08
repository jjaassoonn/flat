import algebra.category.Module.projective
import linear_algebra.free_module.basic
import category_theory.monoidal.tor

import .flat

open category_theory category_theory.limits category_theory.monoidal_category
open_locale direct_sum zero_object

noncomputable theory

universes u v

namespace Module

variables {R : Type u} [comm_ring R] (M : Module.{u} R) [Π (N : Module.{u} R), decidable_eq N]

@[reducible]
def afree : Module.{u} R := Module.of R $ ⨁ (m : M), R

instance afree_is_free : module.free R M.afree :=
module.free.dfinsupp R _

instance afree_is_projective : projective M.afree :=
projective_of_free.{u u u} (module.free.choose_basis R M.afree)

@[reducible]
def from_afree : M.afree ⟶ M :=
direct_sum.to_module _ _ _ $ λ m, 
{ to_fun := λ r, r • m,
  map_add' := λ _ _, add_smul _ _ m,
  map_smul' := λ _ _, by rw [smul_eq_mul, mul_smul, ring_hom.id_apply] }

lemma from_afree_surj : function.surjective M.from_afree :=
λ x, ⟨direct_sum.of (λ (m : M), R) x 1, by 
  erw [direct_sum.to_module_lof, linear_map.coe_mk, one_smul]⟩

instance from_afree_epi : epi M.from_afree :=
(Module.epi_iff_surjective _).mpr $ M.from_afree_surj

@[reducible] def free_res.chain_complex.Xd_aux : 
ℕ → Σ' (N_prev N_next : Module.{u} R) (h : module.free R N_prev ∧ module.free R N_next), N_next ⟶ N_prev :=
@nat.rec (λ _, Σ' (N_prev N_next : Module.{u} R) (h : module.free R N_prev ∧ module.free R N_next), N_next ⟶ N_prev)
⟨M.afree, (kernel M.from_afree).afree, 
  ⟨Module.afree_is_free _, Module.afree_is_free _⟩, 
  Module.from_afree _ ≫ kernel.ι _⟩ $ λ n P, 
⟨P.2.1, (kernel P.2.2.2).afree, ⟨P.2.2.1.2, Module.afree_is_free _⟩, Module.from_afree _ ≫ kernel.ι _⟩


@[reducible] def free_res.chain_complex.X' (n : ℕ) : Module.{u} R :=
(free_res.chain_complex.Xd_aux M n).1

@[reducible] def free_res.chain_complex.d' (i j : ℕ) :
  free_res.chain_complex.X' M i ⟶ free_res.chain_complex.X' M j :=
if h : j + 1 = i
then (eq_to_hom $ by rw h : _ ⟶ free_res.chain_complex.X' M (j + 1)) ≫ 
  (free_res.chain_complex.Xd_aux M _).2.2.2 
else 0

@[simps] def free_res.chain_complex : chain_complex (Module R) ℕ :=
{ X := free_res.chain_complex.X' M,
  d := free_res.chain_complex.d' M,
  shape' := λ i j (h : _ ≠ _), by rw [free_res.chain_complex.d', dif_neg h],
  d_comp_d' := λ i j k (hij : _ = _) (hjk : _ = _), 
  begin 
    substs hij hjk,
    rw [free_res.chain_complex.d', free_res.chain_complex.d', dif_pos rfl, dif_pos rfl, eq_to_hom_refl, 
      eq_to_hom_refl, category.id_comp, category.id_comp],
    dsimp,
    suffices : (free_res.chain_complex.Xd_aux M (k + 1)).2.2.2 ≫ (free_res.chain_complex.Xd_aux M k).2.2.2 = 0,
    { convert this, },
    { change (_ ≫ _) ≫ _ = 0,
      erw [category.assoc, kernel.condition, comp_zero], },
  end }

@[reducible]
def free_res : ProjectiveResolution M :=
{ complex := free_res.chain_complex M,
  π := (chain_complex.to_single₀_equiv (free_res.chain_complex M) M).symm ⟨M.from_afree, 
  begin 
    dsimp only [free_res.chain_complex.d', free_res.chain_complex_d],
    erw [dif_pos (zero_add 1), category.assoc, category.assoc, kernel.condition, comp_zero],
  end⟩,
  projective := λ n, projective_of_free.{u u u} (@@module.free.choose_basis R _ _ _ _ ((free_res.chain_complex.Xd_aux M) n).2.2.1.1),
  exact₀ := 
  begin 
    dsimp [free_res.chain_complex.d'],
    simp only [eq_self_iff_true, category.id_comp, if_true],
    change exact (Module.from_afree _ ≫ _) M.from_afree,
    exact exact_epi_comp exact_kernel_ι,
  end,
  exact := λ n, 
  begin 
    dsimp [free_res.chain_complex.d'],
    simp only [eq_self_iff_true, category.id_comp, if_true],
    suffices : exact (free_res.chain_complex.Xd_aux M (n + 1)).snd.snd.snd 
      (free_res.chain_complex.Xd_aux M n).snd.snd.snd,
    { exact this },
    change exact (_ ≫ _) _,
    convert @@exact_epi_comp _ (infer_instance : has_images (Module.{u} R)) _ _ 
      exact_kernel_ι (Module.from_afree_epi _),
  end,
  epi := M.from_afree_epi }

instance enough_projective_ : enough_projectives (Module.{u} R) :=
Module.Module_enough_projectives.{u u}

instance has_projective_resolutions : has_projective_resolutions (Module.{u} R) := 
{ out := λ Z, ⟨nonempty.intro $ Z.free_res⟩ }

def higher_Tor'_zero_of_flat (h : module.flat.exact R M) (N : Module.{u} R) (n : ℕ) (hn : 0 < n) : 
  ((Tor' (Module.{u} R) n).obj N).obj M ≅ 0 :=
begin 
  dsimp only [Tor', functor.flip],
  refine functor.left_derived_obj_iso (tensor_right M) n N.free_res ≪≫ _,
  suffices : epi _,
  { refine @@cokernel.of_epi _ _ _ _ _ this, },
  suffices : category_theory.exact _ _,
  { exact this.2 },
  dunfold homological_complex.d_to homological_complex.d_from,
  dsimp [functor.map_homological_complex_obj_d],
  dunfold tensor_hom,
  dunfold monoidal_category.tensor_hom,
  refine h (free_res.chain_complex.d' N ((complex_shape.down ℕ).prev n) n) _ _,
  rw complex_shape.prev_eq',
  work_on_goal 3 { exact n + 1 },
  work_on_goal 2 { rw complex_shape.down_rel, },
  rw complex_shape.next_eq',
  work_on_goal 3 { exact n.pred },
  work_on_goal 2 
  { rw complex_shape.down_rel, refine nat.succ_pred_eq_of_pos hn, },

  convert (N.free_res).exact (n - 1) using 2,
  { linarith, },
  { linarith, },
  { linarith, },
  { linarith, },
  { linarith, },
end

def first_Tor'_zero_of_flat (h : module.flat.exact R M) (N : Module.{u} R) : 
  ((Tor' (Module.{u} R) 1).obj N).obj M ≅ 0 :=
M.higher_Tor'_zero_of_flat h N 1 (by linarith)

end Module