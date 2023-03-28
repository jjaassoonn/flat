import algebra.homology.homological_complex
import category_theory.abelian.exact
import algebra.category.Module.abelian

import .test

noncomputable theory

universes v u

open category_theory category_theory.category category_theory.limits

variables {α β : Type*}
variables (V : Type u) [category.{v} V] [has_zero_morphisms V]

section

def complex_shape.not_rfl (a : complex_shape α) : Prop :=
∀ (i : α), ¬ a.rel i i

def complex_shape.not_rfl.ne {a : complex_shape α} (ha : a.not_rfl) {i i' : α} :
  a.rel i i' → i ≠ i' :=
begin 
  contrapose!,
  rintro rfl,
  exact ha _,
end

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

variables {V}  {γ : Type*} (a : complex_shape α) (b : complex_shape β) (c : complex_shape γ)

class has_sign :=
(sign : α → zmod 2)
(rel : ∀ (i i' : α), a.rel i i' → sign i = - (sign i'))

section

instance [has_sign a] (T : Type*) [has_neg T] : has_smul α T :=
{ smul := λ x f, if has_sign.sign a x = 0 then f else - f }

lemma has_sign.smul_zero [has_sign a] (T : Type*) [add_comm_group T]
  (x : α) : x • (0 : T) = 0 :=
begin 
  dunfold has_smul.smul,
  dsimp,
  split_ifs;
  abel,
end

lemma has_sign.smul_eq_zero [has_sign a] (T : Type*) [add_comm_group T] (x : α) (t : T) : 
  x • t = 0 ↔ t = 0 :=
begin
  split,
  { intros h,
    dunfold has_smul.smul at h,
    dsimp at h,
    split_ifs at h,
    { exact h },
    { rwa neg_eq_zero at h, }, },
  { rintro rfl, rw has_sign.smul_zero }
end

lemma has_sign.smul_comp [has_sign a] [preadditive V] (i : α) 
  {v₁ v₂ v₃ : V} (f : v₁ ⟶ v₂) (g : v₂ ⟶ v₃) :
  (i • f) ≫ g = i • (f ≫ g) :=
begin 
  dunfold has_smul.smul,
  dsimp,
  split_ifs,
  { refl },
  { rw preadditive.neg_comp },
end


local attribute [instance] concrete_category.has_coe_to_fun
local attribute [instance] concrete_category.has_coe_to_sort


class has_hadd :=
(add' {} : α → β → γ)
(rel_h' {} : ∀ (i₁ i₂ : α) (j : β), a.rel i₁ i₂ ↔ c.rel (add' i₁ j) (add' i₂ j))
(rel_v' {} : ∀ (i : α) (j₁ j₂ : β), b.rel j₁ j₂ ↔ c.rel (add' i j₁) (add' i j₂))
(add_cancel_h' : ∀ (i₁ i₂ : α) (j : β), add' i₁ j = add' i₂ j ↔ i₁ = i₂)
(add_cancel_v' : ∀ (i : α) (j₁ j₂ : β), add' i j₁ = add' i j₂ ↔ j₁ = j₂)
(balanced' : ∀ (i : α) (j : β) (k' : γ), c.rel (add' i j) k' → 
  ((∃ j', k' = add' i j') ↔ (∃ i', k' = add' i' j)))

notation (name := hadd.add) i `+[` a, b, c`]` j := (has_hadd.add' a b c i j)
variables [has_hadd a b c]

variables {a b c} [decidable_eq α] [decidable_eq β] [decidable_eq γ]

def D_h (C : homological_bicomplex V a b) (i₁ i₂ : α) (j₁ j₂ : β) :
  C.X i₁ j₁ ⟶ C.X i₂ j₂ :=
C.d_h i₁ j₁ j₂ ≫ if h : i₁ = i₂ then eq_to_hom (by rw h) else 0

def D_v (C : homological_bicomplex V a b) (i₁ i₂ : α) (j₁ j₂ : β) :
  C.X i₁ j₁ ⟶ C.X i₂ j₂ :=
C.d_v j₁ i₁ i₂ ≫ if h : j₁ = j₂ then eq_to_hom (by rw h) else 0

@[simp] lemma d_comp_d_v (C : homological_bicomplex V a b) (j : β) (i₁ i₂ i₃ : α) :
  C.d_v j i₁ i₂ ≫ C.d_v j i₂ i₃ = 0 := 
begin 
  by_cases h₁₂ : a.rel i₁ i₂,
  { refine (em (a.rel i₂ i₃)).elim (λ h₂₃, C.d_comp_d_v' j i₁ i₂ i₃ h₁₂ h₂₃) (λ h₂₃, _),
    rw [C.shape_v j _ _ h₂₃, comp_zero], },
  rw [C.shape_v _ _ _ h₁₂, zero_comp],
end

lemma D_v_of_eq (C : homological_bicomplex V a b) 
  (i₁ i₂ : α) (j₁ j₂ : β) (h : j₁ = j₂) :
  C.D_v i₁ i₂ j₁ j₂ = C.d_v j₁ i₁ i₂ ≫ eq_to_hom (by rw h) :=
by rw [D_v, dif_pos h]
 
lemma D_v_of_ne (C : homological_bicomplex V a b) 
  (i₁ i₂ : α) (j₁ j₂ : β) (h : j₁ ≠ j₂) :
  C.D_v i₁ i₂ j₁ j₂ = 0 :=
by rw [D_v, dif_neg h, comp_zero]

lemma D_comp_D_v (C : homological_bicomplex V a b) 
  (i₁ i₂ i₃ : α) (j₁ j₂ j₃ : β) :
  C.D_v i₁ i₂ j₁ j₂ ≫ C.D_v i₂ i₃ j₂ j₃ = 0 :=
begin 
  rw [D_v, D_v],
  split_ifs with h1 h2,
  { substs h1 h2,
    rw [eq_to_hom_refl, eq_to_hom_refl, comp_id, comp_id, d_comp_d_v], },
  all_goals { simp only [comp_zero, zero_comp], },
end 

@[simp] lemma d_comp_d_h (C : homological_bicomplex V a b) (i : α) (j₁ j₂ j₃ : β) :
  C.d_h i j₁ j₂ ≫ C.d_h i j₂ j₃ = 0 := 
begin 
  by_cases h₁₂ : b.rel j₁ j₂,
  { refine (em (b.rel j₂ j₃)).elim (λ h₂₃, C.d_comp_d_h' i j₁ j₂ j₃ h₁₂ h₂₃) (λ h₂₃, _),
    rw [C.shape_h i _ _ h₂₃, comp_zero], },
  rw [C.shape_h _ _ _ h₁₂, zero_comp],
end

lemma D_h_of_eq (C : homological_bicomplex V a b) 
  (i₁ i₂ : α) (j₁ j₂ : β) (h : i₁ = i₂) :
  C.D_h i₁ i₂ j₁ j₂ = C.d_h i₁ j₁ j₂ ≫ eq_to_hom (by rw h) :=
by rw [D_h, dif_pos h]
 
lemma D_h_of_ne (C : homological_bicomplex V a b) 
  (i₁ i₂ : α) (j₁ j₂ : β) (h : i₁ ≠ i₂) :
  C.D_h i₁ i₂ j₁ j₂ = 0 :=
by rw [D_h, dif_neg h, comp_zero]

lemma D_comp_D_h (C : homological_bicomplex V a b) 
  (i₁ i₂ i₃ : α) (j₁ j₂ j₃ : β) :
  C.D_h i₁ i₂ j₁ j₂ ≫ C.D_h i₂ i₃ j₂ j₃ = 0 :=
begin 
  rw [D_h, D_h],
  split_ifs with h1 h2,
  { substs h1 h2,
    rw [eq_to_hom_refl, eq_to_hom_refl, comp_id, comp_id, d_comp_d_h], },
  all_goals { simp only [comp_zero, zero_comp], },
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

section

variables {R : Type*} [comm_ring R] (C : homological_bicomplex (Module R) a b)
variables (a b c)

@[ext]
structure diagonal (k : γ) :=
(fst : α) (snd : β) (add_eq : (fst +[a, b, c] snd) = k)


open_locale direct_sum big_operators

variables {a b} [∀ k, decidable_eq $ diagonal a b c k]
def total_at (j : γ) : Module R :=
Module.of R $ ⨁ (p : diagonal a b c j), C.X p.fst p.snd

variables [∀ (k' : γ) (i : α), decidable (∃ (j : β), c.rel (i+[a,b,c]j) k')]

def total_d [has_sign a] (k k' : γ) :
  C.total_at c k ⟶ C.total_at c k' :=
direct_sum.to_module _ _ _ $ λ p,
∑ᶠ (q : diagonal a b c k'), 
  (direct_sum.lof R _ _ q).comp 
    (C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd)

lemma total_d_aux.finsupp_aux
  [has_sign a] (k₁ k₂ : γ) (p : diagonal a b c k₁) (q : diagonal a b c k₂) :
  (direct_sum.lof R _ _ q).comp 
    (C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd) = 0 ↔
  (C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd) = 0 :=
begin 
  split,
  { intros h,
    ext1 x,
    have EQ0 := fun_like.congr_fun h x,
    rw [linear_map.zero_apply, linear_map.comp_apply,
      linear_map.add_apply, direct_sum.ext_iff R] at EQ0,
    work_on_goal 2 { intros i, apply_instance, },
    specialize EQ0 q,
    rw [direct_sum.component.lof_self] at EQ0,
    rw [linear_map.add_apply, EQ0, map_zero, linear_map.zero_apply], },
  { intro h, rw [h, linear_map.comp_zero],},
end

lemma total_d_aux.finsupp_aux'
  [has_sign a] (k₁ k₂ : γ) (p : diagonal a b c k₁) (q : diagonal a b c k₂) :
  (direct_sum.lof R _ _ q).comp 
    (C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd) ≠ 0 ↔
  (C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd) ≠ 0 :=
begin 
  split,
  { contrapose!, rw total_d_aux.finsupp_aux, exact id },
  { contrapose!, rw total_d_aux.finsupp_aux, exact id }, 
end

lemma total_d_aux.finsupp_case0_aux [has_sign a] (k₁ k₂ : γ) (p : diagonal a b c k₁)
  (hc : ¬ c.rel k₁ k₂) (q : diagonal a b c k₂) :
  (direct_sum.lof R _ _ q).comp 
    (C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd) = 0 :=
begin 
  rw [show C.D_h p.fst q.fst p.snd q.snd = 0,
  begin 
    rw [D_h],
    split_ifs,
    { rw [C.shape_h, zero_comp],
      contrapose! hc,
      have EQ := (has_hadd.rel_v' _ _ _).mp hc,
      rwa [p.add_eq, h, q.add_eq] at EQ, },
    { rw comp_zero, },
  end, show C.D_v p.fst q.fst p.snd q.snd = 0,
  begin 
    rw [D_v],
    split_ifs,
    { rw [C.shape_v, zero_comp],
      contrapose! hc,
      have EQ := (has_hadd.rel_h' _ _ _).mp hc,
      rwa [p.add_eq, h, q.add_eq] at EQ, },
    { rw comp_zero },
  end, zero_add, has_sign.smul_zero, linear_map.comp_zero],
end


lemma total_d_aux.finsupp_case0 [has_sign a] (j₁ j₂ : γ) (p : diagonal a b c j₁)
  (hc : ¬ c.rel j₁ j₂) : 
(function.support (λ (i : diagonal a b c j₂),
  (direct_sum.lof R (diagonal a b c j₂) (λ (i : diagonal a b c j₂), (C.X i.fst i.snd)) i).comp
    (C.D_h p.fst i.fst p.snd i.snd + p.fst • C.D_v p.fst i.fst p.snd i.snd))).finite :=
begin 
  convert set.finite_empty,
  rw function.support_eq_empty_iff,
  ext1,
  apply total_d_aux.finsupp_case0_aux,
  assumption
end

lemma total_d_aux.finsupp_case1_aux0
  [has_sign a] (a_not_rfl : a.not_rfl)
  (k₁ k₂ : γ) 
  (p : diagonal a b c k₁)
  (hc : c.rel k₁ k₂) (q : diagonal a b c k₂)
  (ha : a.rel p.fst q.fst)  : 
  C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd = 
  p.fst • C.D_v p.fst q.fst p.snd q.snd :=
begin
  rw [D_h, dif_neg (a_not_rfl.ne ha), comp_zero, zero_add],
end


lemma total_d_aux.finsupp_case1_aux1
  [has_sign a] (b_not_rfl : b.not_rfl)
  (k₁ k₂ : γ) 
  (p : diagonal a b c k₁)
  (hc : c.rel k₁ k₂) (q : diagonal a b c k₂)
  (hb : b.rel p.snd q.snd) : 
  C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd = 
  C.D_h p.fst q.fst p.snd q.snd :=
begin
  rw [D_v, dif_neg (b_not_rfl.ne hb), comp_zero, has_sign.smul_zero, add_zero],
end

lemma total_d_aux.finsupp_case1_aux2
  [has_sign a] (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl)
  (k₁ k₂ : γ) 
  (p : diagonal a b c k₁)
  (hc : c.rel k₁ k₂) (q : diagonal a b c k₂)
  (heq : C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd ≠ 0) :
  a.rel p.fst q.fst ∨ b.rel p.snd q.snd :=
begin
  rcases p with ⟨i₁, j₁, h₁⟩,
  rcases q with ⟨i₂, j₂, h₂⟩,
  dsimp at *,
  by_cases ha : i₁ = i₂,
  { subst ha, 
    rw [D_h_of_eq _ _ _ _ _ rfl, eq_to_hom_refl, comp_id] at heq,
    rw [←h₁, ←h₂] at hc,
    right,
    exact (has_hadd.rel_v' _ _ _).mpr hc, },
  { rw [C.D_h_of_ne _ _ _ _ ha, zero_add, has_sign.smul_eq_zero, D_v] at heq,
    split_ifs at heq,
    { subst h,
      rw [←h₁, ←h₂] at hc,
      left,
      exact (has_hadd.rel_h' _ _ _).mpr hc, },
    { rw [comp_zero] at heq,
      exact (heq rfl).elim, } },
end

lemma total_d_aux.finsupp_case1_aux3
  [has_sign a] (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl)
  (k₁ k₂ : γ) 
  (p : diagonal a b c k₁)
  (hc : c.rel k₁ k₂) (q : diagonal a b c k₂)
  (heq : C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd ≠ 0) :
  q.fst = p.fst ∨ q.snd = p.snd :=
begin 
  obtain (h|h) := total_d_aux.finsupp_case1_aux2 c C a_not_rfl b_not_rfl
    k₁ k₂ p hc q heq;
  rcases p with ⟨i₁, j₁, h₁⟩;
  rcases q with ⟨i₂, j₂, h₂⟩;
  dsimp at *;
  rw [←h₁, ←h₂] at hc,
  { right,
    rw (has_hadd.add_cancel_v' _ _ _).mp (c.next_eq hc ((has_hadd.rel_h' i₁ i₂ j₁).mp h)), },
  { left,
    rw (has_hadd.add_cancel_h' _ _ _).mp (c.next_eq hc ((has_hadd.rel_v' i₁ j₁ j₂).mp h)), },
end

lemma total_d_aux.finsupp_case1 
  [has_sign a] (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl)
  (k₁ k₂ : γ) 
  (p : diagonal a b c k₁)
  (hc : c.rel k₁ k₂) : 
(function.support (λ (i : diagonal a b c k₂),
  (direct_sum.lof R (diagonal a b c k₂) (λ i, (C.X i.fst i.snd)) i).comp
    (C.D_h p.fst i.fst p.snd i.snd + p.fst • C.D_v p.fst i.fst p.snd i.snd))).finite :=
begin 
  rcases p with ⟨i₁, j₁, h₁⟩,
  rw function.support,
  simp_rw [total_d_aux.finsupp_aux'],
  dsimp,
  have subset1 : {x : diagonal a b c k₂ | ¬C.D_h i₁ x.fst j₁ x.snd + i₁ • C.D_v i₁ x.fst j₁ x.snd = 0} ⊆ 
    {x : diagonal a b c k₂ | x.fst = i₁ ∨ x.snd = j₁},
  { intros q hq,
    simp only [set.mem_set_of_eq] at hq,
    obtain (H|H) := total_d_aux.finsupp_case1_aux3 c C a_not_rfl b_not_rfl _ _ ⟨i₁, j₁, h₁⟩ hc q hq,
    { left, assumption },
    { right, assumption } },
  have finite1 : set.finite {x : diagonal a b c k₂ | x.fst = i₁ ∨ x.snd = j₁},
  { rw show {x : diagonal a b c k₂ | x.fst = i₁ ∨ x.snd = j₁} =
    {x : diagonal a b c k₂ | x.fst = i₁} ∪ {x : diagonal a b c k₂ | x.snd = j₁}, from rfl,
    refine set.finite.union _ _,
    { refine set.subsingleton.finite _,
      rintros ⟨i₂, j₂, h₂⟩ H₂ ⟨i₂', j₂', h₂'⟩ H₂',
      simp only [set.mem_set_of_eq] at H₂ H₂',
      substs H₂ H₂',
      ext,
      { refl, },
      { dsimp,
        rwa [← h₂', has_hadd.add_cancel_v'] at h₂, }, },
    { refine set.subsingleton.finite _,
      rintros ⟨i₂, j₂, h₂⟩ H₂ ⟨i₂', j₂', h₂'⟩ H₂',
      simp only [set.mem_set_of_eq] at H₂ H₂',
      substs H₂ H₂',
      ext,
      { dsimp,
        rwa [← h₂', has_hadd.add_cancel_h'] at h₂, },
      { refl, }, }, },
  exact finite1.subset subset1,
end

lemma total_d_aux.left_finite (k₁ k₂) (p : diagonal a b c k₁) :
  {x : diagonal a b c k₂ | x.fst = p.1}.finite :=
begin 
  refine set.subsingleton.finite _,
  rintros ⟨i₂, j₂, h₂⟩ H₂ ⟨i₂', j₂', h₂'⟩ H₂',
  simp only [set.mem_set_of_eq] at H₂ H₂',
  substs H₂ H₂',
  ext,
  { refl, },
  { dsimp,
    rwa [← h₂', has_hadd.add_cancel_v'] at h₂, },
end

instance total_d_aux.left_subsingleton (k₁ k₂) (p : diagonal a b c k₁) :
  subsingleton (total_d_aux.left_finite _ k₁ k₂ p).to_finset :=
begin 
  fconstructor,
  rintros ⟨⟨i₂, j₂, h₂⟩, H₂⟩ ⟨⟨i₂', j₂', h₂'⟩, H₂'⟩,
  simp only [set.mem_set_of_eq, set.finite.mem_to_finset] at H₂ H₂',
  substs H₂ H₂',
  ext,
  { refl, },
  { dsimp,
    rwa [← h₂', has_hadd.add_cancel_v'] at h₂, },
end

lemma total_d_aux.right_finite (k₁ k₂) (p : diagonal a b c k₁) :
  {x : diagonal a b c k₂ | x.snd = p.2}.finite :=
begin 
  refine set.subsingleton.finite _,
  rintros ⟨i₂, j₂, h₂⟩ H₂ ⟨i₂', j₂', h₂'⟩ H₂',
  simp only [set.mem_set_of_eq] at H₂ H₂',
  substs H₂ H₂',
  ext,
  { dsimp,
    rwa [← h₂', has_hadd.add_cancel_h'] at h₂, },
  { refl, },
end

instance total_d_aux.right_subsingleton (k₁ k₂) (p : diagonal a b c k₁) :
  subsingleton (total_d_aux.right_finite _ k₁ k₂ p).to_finset :=
begin 
  fconstructor,
  rintros ⟨⟨i₂, j₂, h₂⟩, H₂⟩ ⟨⟨i₂', j₂', h₂'⟩, H₂'⟩,
  simp only [set.finite.mem_to_finset, set.mem_set_of_eq] at H₂ H₂',
  substs H₂ H₂',
  ext,
  { dsimp,
    rwa [← h₂', has_hadd.add_cancel_h'] at h₂, },
  { refl, },
end


lemma total_d_aux.union_finite (k₁ k₂) (p : diagonal a b c k₁) :
  ({x : diagonal a b c k₂ | x.fst = p.1} ∪ {x : diagonal a b c k₂ | x.snd = p.2}).finite :=
begin
  refine set.finite.union _ _,
  { apply total_d_aux.left_finite },
  { apply total_d_aux.right_finite },
end

lemma total_d_aux.finsupp_subset
  [has_sign a] (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl)
  (k₁ k₂ : γ) 
  (p : diagonal a b c k₁) :
(function.support (λ (i : diagonal a b c k₂),
  (direct_sum.lof R (diagonal a b c k₂) (λ i, (C.X i.fst i.snd)) i).comp
    (C.D_h p.fst i.fst p.snd i.snd + p.fst • C.D_v p.fst i.fst p.snd i.snd))) ⊆ 
{x : diagonal a b c k₂ | x.fst = p.1 ∨ x.snd = p.2} :=
begin
  by_cases hc : (c.rel k₁ k₂),
  {  rcases p with ⟨i₁, j₁, h₁⟩,
    rw function.support,
    simp_rw [total_d_aux.finsupp_aux'],
    intros q hq,
    simp only [set.mem_set_of_eq] at hq,
    obtain (H|H) := total_d_aux.finsupp_case1_aux3 c C a_not_rfl b_not_rfl _ _ ⟨i₁, j₁, h₁⟩ hc q hq,
    { left, assumption },
    { right, assumption } },
  { convert set.empty_subset _,
    rw function.support_eq_empty_iff,
    ext1,
    apply total_d_aux.finsupp_case0_aux,
    assumption },
end


lemma total_d_aux.finsupp
  [has_sign a] (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl)
  (k₁ k₂ : γ) 
  (p : diagonal a b c k₁) : 
(function.support (λ (i : diagonal a b c k₂),
  (direct_sum.lof R (diagonal a b c k₂) (λ (i : diagonal a b c k₂), (C.X i.fst i.snd)) i).comp
    (C.D_h p.fst i.fst p.snd i.snd + p.fst • C.D_v p.fst i.fst p.snd i.snd))).finite :=
begin 
  by_cases hc : c.rel k₁ k₂,
  { apply total_d_aux.finsupp_case1; assumption },
  { apply total_d_aux.finsupp_case0; assumption },
end

lemma total_d_eq_sum [has_sign a] 
  (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl)
  (k k' : γ) :
  C.total_d c k k' = 
direct_sum.to_module _ _ _ (λ p, 
∑ (q : diagonal a b c k') in (total_d_aux.union_finite _ k k' p).to_finset, 
  (direct_sum.lof R _ _ q).comp 
    (C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd)) := 
begin
  rw [total_d],
  congr' 1,
  ext1 p,
  rw finsum_eq_sum_of_support_subset,
  simp only [set.finite.coe_to_finset],
  apply total_d_aux.finsupp_subset;
  try { assumption },
end


lemma total_d_eq_sum' [has_sign a] 
  (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl)
  (k k' : γ) :
  C.total_d c k k' = 
direct_sum.to_module _ _ _ (λ p, 
∑ (q : diagonal a b c k') in ((total_d_aux.left_finite _ k k' p).to_finset ∪ (total_d_aux.right_finite _ k k' p).to_finset), 
  (direct_sum.lof R _ _ q).comp 
    (C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd)) := 
begin
  rw [total_d_eq_sum];
  try { assumption },
  congr' 1,
  ext1,
  refine finset.sum_congr _ _,
  { ext z,
    simp only [set.finite.mem_to_finset, set.mem_union, finset.mem_union], },
  { intros, refl, }
end

lemma total_d_eq_sum_of_rel [has_sign a] 
  (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl) (c_not_rfl : c.not_rfl)
  (k k' : γ) (hc : c.rel k k') :
  C.total_d c k k' = 
direct_sum.to_module _ _ _ (λ p, 
∑ (q : diagonal a b c k') in ((total_d_aux.left_finite _ k k' p).to_finset.disj_union 
  (total_d_aux.right_finite _ k k' p).to_finset) 
  begin 
    rw finset.disjoint_iff_inter_eq_empty,
    rw finset.eq_empty_iff_forall_not_mem,
    intros z hz,
    simp only [finset.mem_inter, set.finite.mem_to_finset, set.mem_set_of_eq] at hz,
    have := z.add_eq,
    rw [hz.1, hz.2, p.add_eq] at this,
    exact c_not_rfl.ne hc this,
  end, 
  (direct_sum.lof R _ _ q).comp 
    (C.D_h p.fst q.fst p.snd q.snd + p.fst • C.D_v p.fst q.fst p.snd q.snd)) := 
begin
  rw [total_d_eq_sum'];
  try { assumption },
  congr' 1,
  ext1,
  refine finset.sum_congr _ _,
  { ext z,
    simp only [finset.disj_union_eq_union], },
  { intros, refl, }
end

variables [∀ i k', decidable (∃ (q : diagonal a b c k'), q.fst = i)]
variables [∀ i k', decidable (∃ (q : diagonal a b c k'), q.snd = i)]

section


variables {c}

@[simps]
def diagonal.from_balancing1
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k')
  (q : diagonal a b c k') (hq : q.1 = p.1) :
  diagonal a b c k' :=
{ fst := ((has_hadd.balanced' p.1 p.2 k' (by rwa p.add_eq : c.rel (p.1+[a,b,c]p.2) k')).mp
      ⟨q.2, by rw [← hq, q.add_eq]⟩).some,
  snd := p.2,
  add_eq := begin 
    generalize_proofs h,
    exact h.some_spec.symm,
  end }


@[simps]
def diagonal.from_balancing1'
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k')
  (q : diagonal a b c k') (hq : q.1 = p.1) :
  diagonal a b c k' :=
{ fst := a.next p.1,
  snd := p.2,
  add_eq := begin 
    suffices : 
    ((has_hadd.balanced' p.1 p.2 k' (by rwa p.add_eq : c.rel (p.1+[a,b,c]p.2) k')).mp
      ⟨q.2, by rw [← hq, q.add_eq]⟩).some = a.next p.1,
    { rw ← this, 
      generalize_proofs h,
      exact h.some_spec.symm },
    generalize_proofs h,
    have : c.rel (p.1 +[a,b,c] p.2) (h.some +[a,b,c] p.snd),
    { rw p.add_eq,
      convert hc,
      exact h.some_spec.symm },
    rw ← has_hadd.rel_h' at this,
    rwa a.next_eq',
  end }

lemma diagonal.from_balancing1_uniq
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k')
  (q : diagonal a b c k') (hq : q.1 = p.1)
  (q' : diagonal a b c k') 
  (hq' : q'.2 = p.2) :
  p.from_balancing1 hc q hq = q' :=
begin
  ext,
  { dsimp,
    generalize_proofs h,
    have := h.some_spec,
    simp_rw ←q'.add_eq at this, 
    simp_rw hq' at this,
    rw has_hadd.add_cancel_h' at this,
    convert this.symm,
    ext,
    rw [← hq', q'.add_eq], },
  { dsimp, rw [←hq'], }
end

lemma diagonal.from_balancing1_fst_eq {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k')
  (q : diagonal a b c k') (hq : q.1 = p.1) :
  (p.from_balancing1 hc q hq).fst = a.next p.1 :=
begin 
  rw p.from_balancing1_uniq hc q hq (p.from_balancing1' hc q hq) rfl,
  refl,
end

@[simps]
def diagonal.from_balancing2
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k')
  (q : diagonal a b c k') (hq : q.2 = p.2) :
  diagonal a b c k' :=
{ fst := p.1,
  snd := ((has_hadd.balanced' p.1 p.2 k' (by rwa p.add_eq : c.rel (p.1+[a,b,c]p.2) k')).mpr
      ⟨q.1, by rw [← hq, q.add_eq]⟩).some,
  add_eq := begin 
    generalize_proofs h,
    exact h.some_spec.symm,
  end }


lemma diagonal.from_balancing2_uniq
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k')
  (q : diagonal a b c k') (hq : q.2 = p.2)
  (q' : diagonal a b c k') 
  (hq' : q'.1 = p.1) :
  p.from_balancing2 hc q hq = q' :=
begin
  ext,
  { dsimp, rw [←hq'], },
  { dsimp,
    generalize_proofs h,
    have := h.some_spec,
    simp_rw ←q'.add_eq at this, 
    simp_rw hq' at this,
    rw has_hadd.add_cancel_v' at this,
    convert this.symm,
    ext,
    rw [← hq', q'.add_eq], },
end

@[simps]
def diagonal.from_balancing2'
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k')
  (q : diagonal a b c k') (hq : q.2 = p.2) :
  diagonal a b c k' :=
{ fst := p.1,
  snd := b.next p.2,
  add_eq := begin 
    suffices : 
    ((has_hadd.balanced' p.1 p.2 k' (by rwa p.add_eq : c.rel (p.1+[a,b,c]p.2) k')).mpr
      ⟨q.1, by rw [← hq, q.add_eq]⟩).some = b.next p.2,
    { rw ← this, 
      generalize_proofs h,
      exact h.some_spec.symm },
    generalize_proofs h,
    have : c.rel (p.1 +[a,b,c] p.2) (p.1 +[a,b,c] h.some),
    { rw p.add_eq,
      convert hc,
      exact h.some_spec.symm },
    rw ← has_hadd.rel_v' at this,
    rwa b.next_eq',
  end }

lemma diagonal.from_balancing2_snd_eq {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k')
  (q : diagonal a b c k') (hq : q.2 = p.2) :
  (p.from_balancing2 hc q hq).snd = b.next p.2 :=
begin 
  rw p.from_balancing2_uniq hc q hq (p.from_balancing2' hc q hq) rfl,
  refl,
end

end

lemma total_d_eq_ite_of_rel [has_sign a] 
  (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl) (c_not_rfl : c.not_rfl)
  (k k' : γ) (hc : c.rel k k') :
  C.total_d c k k' = 
direct_sum.to_module _ _ _ (λ p, 
  (if H : ∃ (q : diagonal a b c k'), q.1 = p.1 
  then (direct_sum.lof R _ _ H.some).comp 
    (C.D_h p.fst H.some.fst p.snd H.some.snd)
  else 0) +
  (if H : ∃ (q : diagonal a b c k'), q.2 = p.2
  then (direct_sum.lof R _ _ H.some).comp
    (p.fst • C.D_v p.fst H.some.fst p.snd H.some.snd)
  else 0)) := 
begin
  rw [total_d_eq_sum_of_rel];
  try { assumption },
  congr' 1,
  ext1 p,
  rw finset.sum_disj_union,
  congr' 1,
  { split_ifs with H,
    { rw ← finset.sum_attach,
      erw fintype.sum_subsingleton,
      work_on_goal 2
      { refine ⟨H.some, _⟩,
        simpa only [set.finite.mem_to_finset] using H.some_spec, },
      rw subtype.coe_mk,
      congr' 1,
      convert add_zero _,
      rw has_sign.smul_eq_zero,
      rw D_v_of_ne,
      intro rid,
      refine c_not_rfl.ne hc _,
      rw [← p.add_eq, ← H.some.add_eq, rid],
      congr' 1,
      exact H.some_spec.symm, },
    { convert finset.sum_empty,
      rw [finset.eq_empty_iff_forall_not_mem],
      intros x,
      contrapose! H,
      simp only [set.finite.mem_to_finset, set.mem_set_of_eq] at H,
      refine ⟨x, H⟩, }, },
  { split_ifs with H,
    { rw ← finset.sum_attach,
      erw fintype.sum_subsingleton,
      work_on_goal 2
      { refine ⟨H.some, _⟩,
        simpa only [set.finite.mem_to_finset] using H.some_spec, },
      rw subtype.coe_mk,
      congr' 1,
      convert zero_add _,
      rw D_h_of_ne,
      intro rid,
      refine c_not_rfl.ne hc _,
      rw [← p.add_eq, ← H.some.add_eq, rid],
      congr' 1,
      exact H.some_spec.symm, },
    { convert finset.sum_empty,
      rw [finset.eq_empty_iff_forall_not_mem],
      intros x,
      contrapose! H,
      simp only [set.finite.mem_to_finset, set.mem_set_of_eq] at H,
      refine ⟨x, H⟩, }, },
end

lemma has_sign.smul_apply [has_sign a] (i : α) 
  {v₁ v₂ : Module R} (f : v₁ ⟶ v₂) (x)  :
  (i • f) x = i • (f x) :=
begin 
  dunfold has_smul.smul,
  dsimp,
  split_ifs,
  { refl },
  { rw linear_map.neg_apply, },
end

lemma has_sign.map_smul [has_sign a] (i : α) 
  {v₁ v₂ : Module R} (f : v₁ ⟶ v₂) (x)  :
  f (i • x) = i • (f x) :=
begin 
  dunfold has_smul.smul,
  dsimp,
  split_ifs,
  { refl },
  { rw map_neg, },
end


lemma total_d_eq_ite_of_rel' [has_sign a] 
  (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl) (c_not_rfl : c.not_rfl)
  (k k' : γ) (hc : c.rel k k') :
  C.total_d c k k' = 
direct_sum.to_module _ _ _ (λ p, 
  if H : ∃ (q : diagonal a b c k'), q.1 = p.1 
  then (direct_sum.lof R _ _ H.some).comp 
    (C.D_h p.fst H.some.fst p.snd H.some.snd) +
      (direct_sum.lof R _ _ (p.from_balancing1 hc H.some H.some_spec)).comp
    (p.fst • C.D_v p.fst (p.from_balancing1 hc H.some H.some_spec).fst p.snd 
      (p.from_balancing1 hc H.some H.some_spec).snd)
  else 0) := 
begin 
  rw [total_d_eq_ite_of_rel]; try { assumption },
  congr' 1,
  ext1 p,
  by_cases H : ∃ (q : diagonal a b c k'), q.fst = p.fst,
  { have H' : ∃ (q : diagonal a b c k'), q.snd = p.snd,
    { refine ⟨p.from_balancing1 hc H.some H.some_spec, rfl⟩, },
    rw [dif_pos H, dif_pos H', dif_pos H],
    congr' 1,
    suffices EQ : H'.some = p.from_balancing1 hc H.some H.some_spec,
    { rw EQ, },
    { symmetry,
      apply diagonal.from_balancing1_uniq,
      exact H'.some_spec, }, },
  { rw [dif_neg H, zero_add, dif_neg H, dif_neg],
    contrapose! H,
    refine ⟨p.from_balancing2 hc H.some H.some_spec, rfl⟩, },
end


lemma total_d_eq_of_rel [has_sign a] 
  (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl) (c_not_rfl : c.not_rfl)
  (k k' : γ) (hc : c.rel k k') :
  C.total_d c k k' = 
direct_sum.to_module _ _ _ (λ p, 
  if H : ∃ (q : diagonal a b c k'), q.1 = p.1 
  then (direct_sum.lof R _ _ H.some).comp 
    (C.D_h p.fst H.some.fst p.snd H.some.snd) +
      (direct_sum.lof R _ _ (p.from_balancing1' hc H.some H.some_spec)).comp
    (p.fst • C.D_v p.fst (a.next p.fst) p.snd p.snd)
  else 0) := 
begin 
  rw [total_d_eq_ite_of_rel']; try { assumption },
  congr,
  ext1 p,
  by_cases H : ∃ (q : diagonal a b c k'), q.fst = p.fst,
  { rw [dif_pos H, dif_pos H],
    congr' 1,
    suffices EQ : p.from_balancing1 hc H.some H.some_spec = p.from_balancing1' hc H.some H.some_spec,
    { rw EQ, congr' 1 },
    { ext, 
      rw p.from_balancing1_fst_eq hc H.some H.some_spec, refl, 
      refl, }, },
  { rw [dif_neg H, dif_neg H], },
end


lemma D_comp_D_h_apply
  (i₁ i₂ i₃ : α) (j₁ j₂ j₃ : β) (x) :
  C.D_h i₂ i₃ j₂ j₃ (C.D_h i₁ i₂ j₁ j₂ x)  = 0 :=
begin 
  rw [←comp_apply, D_comp_D_h, linear_map.zero_apply],
end

lemma D_comp_D_v_apply
  (i₁ i₂ i₃ : α) (j₁ j₂ j₃ : β) (x) :
  C.D_v i₂ i₃ j₂ j₃ (C.D_v i₁ i₂ j₁ j₂ x)  = 0 :=
begin 
  rw [←comp_apply, D_comp_D_v, linear_map.zero_apply],
end

-- example [has_sign a] 
--   (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl) (c_not_rfl : c.not_rfl)
--   (k₁ k₂ k₃ : γ) (h₁₂ : c.rel k₁ k₂) (h₂₃ : c.rel k₂ k₃) :
--   C.total_d c k₁ k₂ ≫ C.total_d c k₂ k₃ = 0 :=
-- begin 
--   apply direct_sum.linear_map_ext,
--   intros p,
--   ext x : 1,
--   rw [linear_map.zero_comp, linear_map.zero_apply, linear_map.comp_apply, comp_apply,
--     total_d_eq_of_rel, total_d_eq_of_rel];
--   try { assumption },
--   rw [ direct_sum.to_module_lof, linear_map.map_dite],
--   simp_rw [linear_map.add_apply, linear_map.zero_apply],
--   split_ifs with H1,
--   { simp only [map_add, direct_sum.to_module_lof, linear_map.comp_apply, linear_map.dite_apply, 
--       linear_map.add_apply, D_comp_D_h_apply, map_zero, zero_add, linear_map.zero_apply,
--       has_sign.smul_apply, has_sign.map_smul], },
--   -- { rw [linear_map.add_apply, map_add, linear_map.comp_apply, linear_map.comp_apply, 
--   --     direct_sum.to_module_lof, direct_sum.to_module_lof, linear_map.dite_apply,
--   --     linear_map.dite_apply],
--   --   simp_rw [linear_map.add_apply, linear_map.comp_apply, linear_map.zero_apply],
--   --   simp_rw [← comp_apply, D_comp_D_h, linear_map.zero_apply, map_zero, zero_add,
--   --     has_sign.smul_apply, has_sign.map_smul],
--   --   simp_rw [← comp_apply, p.from_balancing1'_fst],
    
--   --   sorry },
--   -- { rw [linear_map.zero_apply, map_zero], },
-- end

example [has_sign a] 
  (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl) (c_not_rfl : c.not_rfl)
  (k₁ k₂ k₃ : γ) (h₁₂ : c.rel k₁ k₂) (h₂₃ : c.rel k₂ k₃) :
  C.total_d c k₁ k₂ ≫ C.total_d c k₂ k₃ = 0 :=
begin 
  apply direct_sum.linear_map_ext,
  intros p,
  ext x : 1,
  rw [linear_map.zero_comp, linear_map.zero_apply, linear_map.comp_apply, comp_apply,
    total_d_eq_ite_of_rel', total_d_eq_ite_of_rel', direct_sum.to_module_lof];
  try { assumption },
  rw [linear_map.map_dite],
  split_ifs with H1,
  { rw [linear_map.add_apply, map_add, linear_map.comp_apply, linear_map.comp_apply, 
      direct_sum.to_module_lof, direct_sum.to_module_lof, linear_map.dite_apply,
      linear_map.dite_apply],
    simp_rw [linear_map.add_apply, linear_map.comp_apply, linear_map.zero_apply],
    simp_rw [← comp_apply, D_comp_D_h, linear_map.zero_apply, map_zero, zero_add,
      has_sign.smul_apply, has_sign.map_smul],
    simp_rw [← comp_apply, D_comp_D_v, linear_map.zero_apply, has_sign.smul_zero, 
      map_zero, add_zero],
    by_cases H2 : ∃ (q : diagonal a b c k₃), q.fst = H1.some.fst,
    { rw (p.from_balancing1_fst_eq h₁₂ H1.some H1.some_spec),
      -- rw [dif_pos H2],
      have h1 : b.rel p.snd H1.some.snd,
      { rwa [← p.add_eq, ← H1.some.add_eq, H1.some_spec, ← has_hadd.rel_v'] at h₁₂, },
      have h2 : c.rel ((p.from_balancing1 h₁₂ H1.some H1.some_spec).fst +[a, b, c] p.snd)
        ((p.from_balancing1 h₁₂ H1.some H1.some_spec).fst +[a,b,c] H1.some.snd),
      { rwa [← has_hadd.rel_v'], },
      have h3 : ((p.from_balancing1 h₁₂ H1.some H1.some_spec).fst +[a,b,c] H1.some.snd) = k₃,
      { erw (p.from_balancing1 h₁₂ H1.some H1.some_spec).add_eq at h2,
        rwa c.next_eq h₂₃ h2, },
      have H3 : ∃ (q : diagonal a b c k₃), q.fst = (p.from_balancing1 h₁₂ H1.some H1.some_spec).fst,
      { refine ⟨⟨(p.from_balancing1 h₁₂ H1.some H1.some_spec).fst, H1.some.snd, h3⟩, rfl⟩, },
      simp_rw (p.from_balancing1_fst_eq h₁₂ H1.some H1.some_spec) at H3,
      rw [dif_pos H2, dif_pos H3],
      generalize_proofs H4 H5,
      generalize_proofs at H4,
      have EQ : H1.some.from_balancing1 h₂₃ H2.some H4 = H3.some,
      { apply H1.some.from_balancing1_uniq,
        have EQ1 := H3.some.add_eq,
        rw H3.some_spec at EQ1,
        simp_rw ←h3 at EQ1,
        rw (p.from_balancing1_fst_eq h₁₂ H1.some H1.some_spec) at EQ1,
        rwa has_hadd.add_cancel_v' at EQ1, },
      rw [EQ],
      rw (p.from_balancing1_snd h₁₂ H1.some H1.some_spec),
      -- convert map_zero _,
      -- simp_rw diagonal.from_balancing1_fst_eq,
      -- sorry 
      },
    sorry { rw [dif_neg H2, dif_neg, add_zero],
      contrapose! H2,
      -- exfalso,
      have h1 : b.rel p.snd H2.some.snd,
      { rw [←(p.from_balancing1 h₁₂ H1.some H1.some_spec).add_eq, ←H2.some.add_eq, H2.some_spec,
          ← has_hadd.rel_v'] at h₂₃,
        exact h₂₃, },
      have h1' : c.rel (p.fst+[a,b,c]p.snd) (p.fst +[a,b,c] H2.some.snd),
      { rwa ←has_hadd.rel_v',  },
      have h2 : b.rel p.snd H1.some.snd,
      { rwa [← p.add_eq, ← H1.some.add_eq, H1.some_spec,
          ← has_hadd.rel_v'] at h₁₂, },
      have h3 : H2.some.snd = H1.some.snd,
      { exact b.next_eq h1 h2 },
      have h4 : c.rel (p.fst+[a,b,c] H1.some.snd) 
        ((p.from_balancing1 h₁₂ H1.some H1.some_spec).fst +[a,b,c] H2.some.snd),
      { convert h₂₃, 
        { convert H1.some.add_eq using 1,
          congr' 1,
          exact H1.some_spec.symm, },
        { convert H2.some.add_eq using 1,
          congr' 1,
          exact H2.some_spec.symm, }, },rw H1.some_spec,
      use H1.some.from_balancing2' h₂₃ H2.some h3,
      exact H1.some_spec, } },
  { rw [linear_map.zero_apply, map_zero], },
end

#exit
/-
 
      p.fst • 
    begin 
      have : ∃ (q : diagonal a b c k'), q.2 = p.2,
      { use p.from_balancing1 hc H.some H.some_spec,
        refl, },
      have := C.D_v p.fst this.some.fst p.snd this.some.2,
    end
-/

lemma total_d_comp_d [has_sign a] 
  (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl) (c_not_rfl : c.not_rfl)
  (k₁ k₂ k₃ : γ) (h₁₂ : c.rel k₁ k₂) (h₂₃ : c.rel k₂ k₃) :
  C.total_d c k₁ k₂ ≫ C.total_d c k₂ k₃ = 0 :=
begin 
  apply direct_sum.linear_map_ext,
  intros p,
  ext x q : 2,
  rw [linear_map.zero_comp, linear_map.zero_apply, linear_map.comp_apply, comp_apply,
    total_d_eq_ite_of_rel, total_d_eq_ite_of_rel, direct_sum.to_module_lof, linear_map.add_apply,
    map_add, direct_sum.zero_apply],
  all_goals { try { assumption } },
  rw [linear_map.map_dite, linear_map.map_dite],
  simp_rw [linear_map.comp_apply, direct_sum.to_module_lof, linear_map.zero_apply, map_zero],
  by_cases H : ¬ (∃ (q : diagonal a b c k₂), q.fst = p.fst) ∧ ¬ (∃ (q : diagonal a b c k₂), q.snd = p.snd),
  { rcases H with ⟨H1, H2⟩,
    rw [dif_neg H1, dif_neg H2, zero_add, direct_sum.zero_apply], },
  rw [not_and_distrib, not_not, not_not] at H,
  rcases H with (H|H),
  { have H' : ∃ (q : diagonal a b c k₂), q.snd = p.snd,
    { refine ⟨p.from_balancing1 h₁₂ H.some H.some_spec, rfl⟩, },
    simp only [dif_pos H, dif_pos H', linear_map.add_apply, linear_map.dite_apply, 
      direct_sum.add_apply, direct_sum.dite_apply R],
    simp_rw [linear_map.comp_apply, ← comp_apply, D_comp_D_h, linear_map.zero_apply,
      map_zero, direct_sum.zero_apply, has_sign.smul_comp],
    rw [dif_eq_if, if_t_t, zero_add],
    convert_to _ + (_ + 0) = (0 : C.X _ _),
    { congr' 2,
      by_cases H'' : ∃ (q : diagonal a b c k₃), q.snd = H'.some.snd,
      { rw [dif_pos H''],
        convert_to (0 : ⨁ (q : diagonal a b c k₃), (C.X q.fst q.snd)) q = 0,
        { congr' 1,
          convert map_zero _,
          rw [has_sign.smul_apply, has_sign.smul_apply, has_sign.map_smul, ←comp_apply, D_comp_D_v,
            linear_map.zero_apply, has_sign.smul_zero, has_sign.smul_zero], },
        { rw direct_sum.zero_apply }, },
      { rw [dif_neg H''], }, },
    rw [add_zero],
    by_cases H'' : ∃ (q : diagonal a b c k₃), q.snd = H.some.snd,
    { rw [dif_pos H'', dif_pos],

      sorry },
    sorry,
    
     },
  sorry
end

#exit
-- @[ext]
-- structure relatable_diagonal ⦃k₁ k₂ : γ⦄ (h : c.rel k₁ k₂) (p : diagonal a b c k₁) :=
-- (to_diagonal : diagonal a b c k₂)
-- (rel : a.rel p.fst to_diagonal.fst ∨ b.rel p.snd to_diagonal.snd)

@[simps]
def relatable_diagonal_horizontal ⦃k₁ k₂ : γ⦄ (h : c.rel k₁ k₂) (p : diagonal a b c k₁)
  ⦃i : α⦄ (ha : a.rel p.fst i) :
  relatable_diagonal k₁ k₂ p :=
{ to_diagonal := 
  { fst := i,
    snd := p.snd,
    add_eq := 
    begin 
      have rel1 := (has_hadd.rel_h' p.fst i p.snd).1 ha,
      rw p.add_eq at rel1,
      rw c.next_eq h rel1,
    end },
  rel := or.intro_left _ ha }

lemma relatable_diagonal_horizontal_uniq ⦃k₁ k₂ : γ⦄ (h : c.rel k₁ k₂) (p : diagonal a b c k₁)
  ⦃i : α⦄ (ha : a.rel p.fst i) 
  (P : relatable_diagonal k₁ k₂ p) (hP : a.rel p.fst P.to_diagonal.fst) :
  P = relatable_diagonal_horizontal h p ha :=
begin 
  have eq1 : P.to_diagonal.fst = i := a.next_eq hP ha,
  ext,
  { exact eq1 },
  { dsimp,
    have eq3 : (i+[a,b,c]p.snd) = k₂ := (relatable_diagonal_horizontal h p ha).to_diagonal.add_eq,
    rw [← P.to_diagonal.add_eq, eq1, has_hadd.add_cancel_v'] at eq3,
    rw eq3, },
end

@[simps]
def relatable_diagonal_vertical ⦃k₁ k₂ : γ⦄ (h : c.rel k₁ k₂) (p : diagonal a b c k₁)
  ⦃j : β⦄ (hb : b.rel p.snd j) :
  relatable_diagonal k₁ k₂ p :=
{ to_diagonal := 
  { fst := p.fst,
    snd := j,
    add_eq := 
    begin 
      have rel1 := (has_hadd.rel_v' p.fst p.snd j).1 hb,
      rw p.add_eq at rel1,
      rw c.next_eq h rel1,
    end },
  rel := or.intro_right _ hb }

lemma relatable_diagonal_vertical_uniq ⦃k₁ k₂ : γ⦄ (h : c.rel k₁ k₂) (p : diagonal a b c k₁)
  ⦃j : β⦄ (hb : b.rel p.snd j) 
  (P : relatable_diagonal k₁ k₂ p) (hP : b.rel p.snd P.to_diagonal.snd) :
  P = relatable_diagonal_vertical h p hb :=
begin 
  have eq1 : P.to_diagonal.snd = j := b.next_eq hP hb,
  ext,
  { dsimp, 
    have eq3 : (p.fst+[a,b,c]j) = k₂ := (relatable_diagonal_vertical h p hb).to_diagonal.add_eq,
    rw [← P.to_diagonal.add_eq, eq1, has_hadd.add_cancel_h'] at eq3,
    rw eq3, },
  { exact eq1 },
end

lemma relatable_diagonal_either_or ⦃k₁ k₂ : γ⦄ (h : c.rel k₁ k₂) (p : diagonal a b c k₁)
  (P : relatable_diagonal k₁ k₂ p) :
  (∃ (i : α) (ha : a.rel p.fst i), P = relatable_diagonal_horizontal h p ha) ∨
  (∃ (j : β) (hb : b.rel p.snd j), P = relatable_diagonal_vertical h p hb) :=
begin 
  rcases P with ⟨⟨i, j, hij⟩, (hP|hP)⟩,
  { left, 
    refine ⟨i, hP, relatable_diagonal_horizontal_uniq _ _ hP _ _⟩,
    assumption, },
  { right,
    refine ⟨j, hP, relatable_diagonal_vertical_uniq _ _ hP _ _⟩,
    assumption, },
end

lemma relatable_diagonal_of_not_c_rel ⦃k₁ k₂ : γ⦄ (h : ¬ c.rel k₁ k₂) (p : diagonal a b c k₁)

lemma relatable_diagonal_not_both ⦃k₁ k₂ : γ⦄ 
  (a_not_rfl : a.not_rfl) (b_not_rfl : b.not_rfl)
  (h : c.rel k₁ k₂) (p : diagonal a b c k₁)
  (P : relatable_diagonal h p) 
  (i : α) (ha : a.rel p.fst i) (hPa : P = relatable_diagonal_horizontal h p ha)
  (j : β) (hb : b.rel p.snd j) (hPb : P = relatable_diagonal_vertical h p hb) :
  false :=
begin 
  rw hPb at hPa,
  rw [relatable_diagonal.ext_iff, diagonal.ext_iff] at hPa,
  rcases hPa with ⟨h1, h2⟩,
  dsimp at *,
  rw h1 at ha,
  refine a_not_rfl _ ha,
end

-- instance ⦃k₁ k₂ : γ⦄ (h : c.rel k₁ k₂) (p : diagonal a b c k₁) : 
--   finite (relatable_diagonal h p) :=
-- begin 
--   by_cases h1 : ∃ (i : α), a.rel p.fst i,
--   all_goals { by_cases h2 : ∃ (j : β), b.rel p.snd j },
--   { sorry },
--   { sorry },
--   { sorry },
--   { haveI : is_empty (relatable_diagonal h p),
--     { by_contradiction rid,
--       rw not_is_empty_iff at rid,
--       rcases rid with ⟨⟨_, (rid|rid)⟩⟩,
--       { rw not_exists at h1, tauto },
--       { rw not_exists at h2, tauto }, },
--     apply_instance, }
-- end

variables [∀ p q, decidable $ c.rel p q]

def total_d (k₁ k₂ : γ) : C.total_at c k₁ ⟶ C.total_at c k₂ :=
Module.of_hom $ direct_sum.to_module _ _ _ $ λ i, 
{ to_fun := λ x, _,
  map_add' := _,
  map_smul' := _ }
-- if c_rel : c.rel k₁ k₂
-- then Module.of_hom $ direct_sum.to_module _ _ _ $ λ i, 
-- { to_fun := λ x, direct_sum.of _ begin 
--     refine ((relatable_diagonal_horizontal c_rel i) _).to_diagonal,
--   end _,
--   map_add' := _,
--   map_smul' := _ }
-- else 0
-- Module.of_hom $ direct_sum.to_module _ _ _ $ λ i, _

end

end homological_bicomplex

def double_chain_complex (α : Type*) [add_right_cancel_semigroup α] [has_one α] : Type* :=
homological_bicomplex V (complex_shape.down α) (complex_shape.down α)

def double_cochain_complex (α : Type*) [add_right_cancel_semigroup α] [has_one α] : Type* :=
homological_bicomplex V (complex_shape.up α) (complex_shape.up α)

namespace double_chain_complex

variables {R : Type*} [comm_ring R] (C : double_chain_complex (Module R) ℤ)

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

lemma total_d_apply_of_even' (m p q : ℤ) (hpq : p + q = m) (x : C.X p q)
  (h : even p) :
  C.total_d m (direct_sum.of (λ (y : diagonal m), C.X y.fst y.snd) ⟨p, q, hpq⟩ x) = 
  direct_sum.of (λ (y : diagonal m), C.X y.fst y.snd) ⟨p - 1, q, by { rw [sub_add_co] }⟩ 
    (C.d_v _ _ _ x) + 
  direct_sum.of (λ (y : diagonal m), C.X y.fst y.snd) ⟨p, q - 1, by ring⟩ 
    (C.d_h _ _ _ x) :=
sorry

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
  ext ⟨a, b, eq1⟩ (x : C.X a b) ⟨a', b', eq2⟩,
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