import algebra.homology.homological_complex
import category_theory.abelian.exact
import algebra.category.Module.abelian

noncomputable theory

universes v u

open category_theory category_theory.category category_theory.limits

variables {α β : Type*}
variables (V : Type u) [category.{v} V] [has_zero_morphisms V]

section

structure homological_bicomplex (a : complex_shape α) (b : complex_shape β) :=
(X : α → β → V)
(d_h : Π (i : α) (j j' : β), X i j ⟶ X i j')
(shape_h' : ∀ (i : α) (j j' : β), ¬ b.rel j j' → d_h i j j' = 0)
(d_v : Π (j : β) (i i' : α), X i j ⟶ X i' j)
(shape_v' : ∀ (j : β) (i i' : α), ¬ a.rel i i' → d_v j i i' = 0)
(d_comp_d_v' : ∀ (j : β) (i₁ i₂ i₃ : α), a.rel i₁ i₂ → a.rel i₂ i₃ → 
  d_v j i₁ i₂ ≫ d_v j i₂ i₃ = 0)
(d_comp_d_h' : ∀ (i : α) (j₁ j₂ j₃ : β), b.rel j₁ j₂ → b.rel j₂ j₃ → 
  d_h i j₁ j₂ ≫ d_h i j₂ j₃ = 0)
(comm' : ∀ (i₁ i₂ : α) (j₁ j₂ : β), a.rel i₁ i₂ → b.rel j₁ j₂ → 
  d_v j₁ i₁ i₂ ≫ d_h i₂ j₁ j₂ = d_h i₁ j₁ j₂ ≫ d_v j₂ i₁ i₂)

end

namespace homological_bicomplex

restate_axiom shape_h'
restate_axiom shape_v'
restate_axiom comm'
attribute [simp] shape_h shape_v

variables {V} {a : complex_shape α} {b : complex_shape β}

@[simp] lemma d_comp_d_v (C : homological_bicomplex V a b) (j : β) (i₁ i₂ i₃ : α) :
  C.d_v j i₁ i₂ ≫ C.d_v j i₂ i₃ = 0 := 
begin 
  by_cases h₁₂ : a.rel i₁ i₂,
  { refine (em (a.rel i₂ i₃)).elim (λ h₂₃, C.d_comp_d_v' j i₁ i₂ i₃ h₁₂ h₂₃) (λ h₂₃, _),
    rw [C.shape_v j _ _ h₂₃, comp_zero], },
  rw [C.shape_v _ _ _ h₁₂, zero_comp],
end

@[simp] lemma d_comp_d_h (C : homological_bicomplex V a b) (i : α) (j₁ j₂ j₃ : β) :
  C.d_h i j₁ j₂ ≫ C.d_h i j₂ j₃ = 0 := 
begin 
  by_cases h₁₂ : b.rel j₁ j₂,
  { refine (em (b.rel j₂ j₃)).elim (λ h₂₃, C.d_comp_d_h' i j₁ j₂ j₃ h₁₂ h₂₃) (λ h₂₃, _),
    rw [C.shape_h i _ _ h₂₃, comp_zero], },
  rw [C.shape_h _ _ _ h₁₂, zero_comp],
end

@[simps]
def vertical_component (C : homological_bicomplex V a b) (j : β) : homological_complex V a :=
{ X := λ i, C.X i j,
  d := C.d_v j,
  shape' := λ _ _ h, C.shape_v _ _ _ h,
  d_comp_d' := λ _ _ _ _ _, C.d_comp_d_v _ _ _ _ }

@[simps]
def vertical_component_map (C : homological_bicomplex V a b) (j₁ j₂ : β) :
  C.vertical_component j₁ ⟶ C.vertical_component j₂ :=
{ f := λ i, C.d_h i j₁ j₂,
  comm' := 
  begin 
    intros i₁ i₂ h₁₂,
    dsimp,
    by_cases H : b.rel j₁ j₂,
    { exact (C.comm i₁ i₂ j₁ j₂ h₁₂ H).symm, },
    { rw [C.shape_h _ _ _ H, C.shape_h _ _ _ H, zero_comp, comp_zero], },
  end }

@[simps]
def as_vertical_complex (C : homological_bicomplex V a b) : 
  homological_complex (homological_complex V a) b :=
{ X := C.vertical_component,
  d := C.vertical_component_map,
  shape' := λ j₁ j₂ h₁₂, 
  begin 
    ext i,
    simpa only [vertical_component_map_f, homological_complex.zero_apply] using C.shape_h _ _ _ h₁₂,
  end,
  d_comp_d' := by { intros, ext, simp } }

@[simps]
def horizontal_component (C : homological_bicomplex V a b) (i : α) : homological_complex V b :=
{ X := C.X i,
  d := C.d_h i,
  shape' := λ _ _ h, C.shape_h _ _ _ h,
  d_comp_d' := λ _ _ _ _ _, C.d_comp_d_h _ _ _ _ }

@[simps]
def horizontal_component_map (C : homological_bicomplex V a b) (i₁ i₂ : α) :
  C.horizontal_component i₁ ⟶ C.horizontal_component i₂ :=
{ f := λ j, C.d_v j i₁ i₂,
  comm' := 
  begin 
    intros j₁ j₂ h₁₂,
    dsimp,
    by_cases H : a.rel i₁ i₂,
    { exact C.comm _ _ _ _ H h₁₂, },
    { rw [C.shape_v _ _ _ H, C.shape_v _ _ _ H, zero_comp, comp_zero], },
  end }

@[simps]
def as_horizontal_complex (C : homological_bicomplex V a b) :
  homological_complex (homological_complex V b) a :=
{ X := C.horizontal_component,
  d := C.horizontal_component_map,
  shape' := λ i₁ i₂ h₁₂, 
  begin 
    ext j,
    simpa only [horizontal_component_map_f, homological_complex.zero_apply] using 
      C.shape_v _ _ _ h₁₂,
  end,
  d_comp_d' := by { intros, ext, simp } }

end homological_bicomplex

def double_chain_complex (α : Type*) [add_right_cancel_semigroup α] [has_one α] : Type* :=
homological_bicomplex V (complex_shape.down α) (complex_shape.down α)

def double_cochain_complex (α : Type*) [add_right_cancel_semigroup α] [has_one α] : Type* :=
homological_bicomplex V (complex_shape.up α) (complex_shape.up α)

namespace double_chain_complex

variables {R : Type*} [comm_ring R] (C : double_chain_complex (Module R) ℤ)

-- variables (C : double_chain_complex V ℤ) [has_products.{0} V]

@[ext, derive [decidable_eq]]
structure diagonal (n : ℤ) :=
(fst : ℤ) (snd : ℤ) (add_eq : fst + snd = n)

@[reducible]
def total_at (n : ℤ) : Module R :=
Module.of R $ direct_sum (diagonal n) $ λ p, C.X p.fst p.snd

variables [Π (m : ℤ), decidable $ even m]

def total_d (m : ℤ) : C.total_at m ⟶ C.total_at (m - 1) :=
Module.of_hom $ direct_sum.to_module _ _ _ $ λ p, 
-- vertical component
(direct_sum.lof R (diagonal $ m - 1) (λ p, C.X p.fst p.snd) 
  ⟨p.fst - 1, p.snd, by rw [sub_add_eq_add_sub, p.add_eq]⟩ : 
  C.X (p.fst - 1) p.snd →ₗ[R] 
  direct_sum (diagonal $ m - 1) $ λ p, C.X p.fst p.snd).comp 
(C.d_v p.snd p.fst (p.fst - 1) : C.X p.fst p.snd →ₗ[R] C.X (p.fst - 1) p.snd) + 
-- alternating horizontal component
((if even p.fst then id else has_neg.neg : 
  (C.X p.fst p.snd →ₗ[R] direct_sum (diagonal (m - 1)) (λ p, C.X p.fst p.snd)) →  
  (C.X p.fst p.snd →ₗ[R] direct_sum (diagonal (m - 1)) (λ p, C.X p.fst p.snd))) $
(direct_sum.lof R (diagonal $ m - 1) (λ p, C.X p.fst p.snd) 
  ⟨p.fst, p.snd - 1, by rw [←add_sub_assoc, p.add_eq]⟩ :
  C.X p.fst (p.snd - 1) →ₗ[R]
  direct_sum (diagonal $ m - 1) $ λ p, C.X p.fst p.snd).comp
(C.d_h p.fst p.snd (p.snd - 1) : C.X p.fst p.snd →ₗ[R] C.X p.fst (p.snd - 1)))

lemma total_d_apply_of_even (p q : ℤ) (x : C.X p q) (h : even p) :
  C.total_d (p + q) (direct_sum.of (λ (y : diagonal (p + q)), C.X y.fst y.snd) ⟨p, q, rfl⟩ x) = 
  direct_sum.of (λ (y : diagonal (p + q - 1)), C.X y.fst y.snd) ⟨p - 1, q, by ring⟩ 
    (C.d_v _ _ _ x) + 
  direct_sum.of (λ (y : diagonal (p + q - 1)), C.X y.fst y.snd) ⟨p, q - 1, by ring⟩ 
    (C.d_h _ _ _ x) :=
begin 
  erw direct_sum.to_module_lof,
  simp only [if_pos h, id.def, linear_map.add_apply, linear_map.coe_comp, function.comp_app,
    direct_sum.lof_eq_of],
end

lemma total_d_apply_of_odd (p q : ℤ) (x : C.X p q) (h : ¬ even p) :
  C.total_d (p + q) (direct_sum.of (λ (y : diagonal (p + q)), C.X y.fst y.snd) ⟨p, q, rfl⟩ x) = 
  direct_sum.of (λ (y : diagonal (p + q - 1)), C.X y.fst y.snd) ⟨p - 1, q, by ring⟩ 
    (C.d_v _ _ _ x) -
  direct_sum.of (λ (y : diagonal (p + q - 1)), C.X y.fst y.snd) ⟨p, q - 1, by ring⟩ 
    (C.d_h _ _ _ x) :=
begin 
  erw direct_sum.to_module_lof,
  simp only [if_neg h, linear_map.add_apply, linear_map.coe_comp, function.comp_app, 
    direct_sum.lof_eq_of, linear_map.neg_apply, sub_eq_add_neg],
end

lemma total_d_comp_d (m : ℤ) :
  (C.total_d (m - 1)).comp (C.total_d m) = 0 :=
  -- (0 : direct_sum (diagonal (p + q - 1 - 1)) $ λ p, C.X p.fst p.snd)
begin
  ext ⟨a, b, eq1⟩ x ⟨a', b', eq2⟩,
  simp only [linear_map.comp_apply, linear_map.zero_apply, direct_sum.zero_apply],
end

#exit
example (p q : ℕ) :
  C.X p q ⟶ C.X (p - 1) q :=
C.d_v q p (p - 1)

example (p q : ℤ) :
  C.X p q ⟶ C.X p (q - 1) :=
C.d_h p q (q - 1)

example (p q p' q' : ℤ) :
  C.X p q ⟶ C.X p' q' :=
C.d_h p q q' ≫ C.d_v q' p p'

example (p q p' q' : ℤ) :
  C.X p q ⟶ C.X p' q' :=
C.d_v q p p' ≫ C.d_h p' q q'

example (p q p' q' : ℤ) :
  C.X p q ⟶ C.X p' q' :=
C.d_h p q q' ≫ C.d_v q' p p' + 
if even q 
then C.d_v q p p' ≫ C.d_h p' q q' 
else - C.d_v q p p' ≫ C.d_h p' q q'

def total_complex_direct_sum.d' (n : ℤ) :
  C.total_at n ⟶ C.total_at (n - 1) :=



def total_complex_direct_sum (C : double_chain_complex (Module R) ℤ) : chain_complex (Module R) ℤ :=
{ X := λ n, Module.of R $ direct_sum {p : ℤ × ℤ | p.1 + p.2 = n} (λ p, C.X p.val.fst p.val.snd),
  d := λ i j, Module.of_hom _,
  shape' := _,
  d_comp_d' := _ } 

end double_chain_complex