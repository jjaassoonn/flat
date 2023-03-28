import algebra.homology.homological_complex
import category_theory.abelian.exact
import algebra.category.Module.abelian

import tactic.interval_cases

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
attribute [simp] shape_h shape_v

variables {V}  {γ : Type*} (a : complex_shape α) (b : complex_shape β) (c : complex_shape γ)

class has_sign :=
(sign : α → zmod 2)
(rel : ∀ (i i' : α), a.rel i i' → sign i ≠ sign i')

instance has_sign1 : has_sign (complex_shape.up ℤ) :=
{ sign := λ i, i,
  rel := λ i j,
  begin 
    dsimp,
    rintro rfl h,
    norm_num at h,
  end }

instance has_sign2 : has_sign (complex_shape.up ℕ) :=
{ sign := λ i, i,
  rel := λ i j,
  begin 
    dsimp,
    rintro rfl h,
    norm_num at h,
  end }

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
  ((∃ i', k' = add' i' j) ∧ (∃ j', k' = add' i j')))
/--
This is wrong for example:
in down ℕ
i + 0 -> k' = i - 1
then k' = (i - 1) + 0 is fine but k' = i + j' is bad

I want i + 0 -> k' = i - 1
1 + 0 -> 0
-/

instance test1 : has_hadd (complex_shape.up ℤ) (complex_shape.up ℤ) (complex_shape.up ℤ) :=
{ add' := (+),
  rel_h' := λ _ _ _, begin
    dsimp,
    split,
    { rintro rfl, ring },
    { intros h, linarith, },
  end,
  rel_v' := λ _ _ _, begin
    dsimp,
    split,
    { rintro rfl, ring },
    { intros h, linarith, },
  end,
  add_cancel_h' := λ _ _ _, begin
    split;
    intros;
    linarith,
  end,
  add_cancel_v' := λ _ _ _, begin
    split;
    intros;
    linarith,
  end,
  balanced' := λ i j k' (h : _ = _), 
  begin 
    refine ⟨⟨i + 1, by linarith⟩, ⟨j + 1, by linarith⟩⟩,
  end }

instance test2 : has_hadd (complex_shape.up ℕ) (complex_shape.up ℕ) (complex_shape.up ℕ) :=
{ add' := (+),
  rel_h' := λ _ _ _, begin
    dsimp,
    split,
    { rintro rfl, ring },
    { intros h, linarith, },
  end,
  rel_v' := λ _ _ _, begin
    dsimp,
    split,
    { rintro rfl, ring },
    { intros h, linarith, },
  end,
  add_cancel_h' := λ _ _ _, begin
    split;
    intros;
    linarith,
  end,
  add_cancel_v' := λ _ _ _, begin
    split;
    intros;
    linarith,
  end,
  balanced' := λ i j k' (h : _ = _), 
  begin 
    refine ⟨⟨i + 1, by linarith⟩, ⟨j + 1, by linarith⟩⟩,
  end }

instance test3 : has_hadd (complex_shape.up ℕ) (complex_shape.up ℤ) (complex_shape.up ℤ) :=
{ add' := λ n z, (n : ℤ) + z,
  rel_h' := λ _ _ _, begin
    dsimp,
    split,
    { rintro rfl, norm_num, ring, },
    { intros h, linarith, },
  end,
  rel_v' := λ _ _ _, begin
    dsimp,
    split,
    { rintro rfl, ring },
    { intros h, linarith, },
  end,
  add_cancel_h' := λ _ _ _, begin
    split;
    intros;
    linarith,
  end,
  add_cancel_v' := λ _ _ _, begin
    split;
    intros;
    linarith,
  end,
  balanced' := λ i j k' (h : _ = _), 
  begin 
    refine ⟨⟨i + 1, by norm_num; linarith⟩, ⟨j + 1, by linarith⟩⟩,
  end }

notation (name := hadd.add) i `+[` a, b, c`]` j := (has_hadd.add' a b c i j)
variables [has_hadd a b c]

variables {a b c} [decidable_eq α] [decidable_eq β] [decidable_eq γ]

@[simp] lemma d_comp_d_v (C : homological_bicomplex V a b) (j : β) (i₁ i₂ i₃ : α) :
  C.d_v j i₁ i₂ ≫ C.d_v j i₂ i₃ = 0 := 
begin 
  by_cases h₁₂ : a.rel i₁ i₂,
  { refine (em (a.rel i₂ i₃)).elim (λ h₂₃, C.d_comp_d_v' j i₁ i₂ i₃ h₁₂ h₂₃) (λ h₂₃, _),
    rw [C.shape_v j _ _ h₂₃, comp_zero], },
  rw [C.shape_v _ _ _ h₁₂, zero_comp],
end

@[simp] lemma comm (C : homological_bicomplex V a b) (j₁ j₂ : β) (i₁ i₂ : α) :
  C.d_h i₁ j₁ j₂ ≫ C.d_v j₂ i₁ i₂ = 
  C.d_v j₁ i₁ i₂ ≫ C.d_h i₂ j₁ j₂ := 
begin 
  by_cases ha : a.rel i₁ i₂;
  by_cases hb : b.rel j₁ j₂,
  { rw C.comm'; assumption },
  { rw [C.shape_h, C.shape_h, comp_zero, zero_comp]; assumption },
  { rw [C.shape_v, C.shape_v, comp_zero, zero_comp]; assumption },
  { rw [C.shape_v, C.shape_v, comp_zero, zero_comp]; assumption },
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
    { rw C.comm, },
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
    { rw C.comm, },
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

section defs_in_mod

variables {R : Type*} [comm_ring R] (C : homological_bicomplex (Module R) a b)
variables (a b c)

@[ext]
structure diagonal (k : γ) :=
(fst : α) (snd : β) (add_eq : (fst +[a, b, c] snd) = k)


open_locale direct_sum big_operators

variables {a b} [∀ k, decidable_eq $ diagonal a b c k]
def total_at (j : γ) : Module R :=
Module.of R $ ⨁ (p : diagonal a b c j), C.X p.fst p.snd

@[simps]
def diagonal.from_balancing1
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k') :
  diagonal a b c k' :=
{ fst := (has_hadd.balanced' p.1 p.2 k' (by rwa p.add_eq : c.rel (p.1+[a,b,c]p.2) k')).1.some,
  snd := p.2,
  add_eq := begin 
    generalize_proofs h,
    exact h.some_spec.symm,
  end }

@[simps]
def diagonal.from_balancing1'
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k') :
  diagonal a b c k' :=
{ fst := a.next p.1,
  snd := p.2,
  add_eq := begin 
    suffices : 
      (has_hadd.balanced' p.1 p.2 k' (by rwa p.add_eq : c.rel (p.1+[a,b,c]p.2) k')).1.some = 
      a.next p.1,
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

lemma diagonal.from_balancing1'_rel
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k') :
  a.rel p.1 (a.next p.1) :=
begin 
  have EQ1 := (p.from_balancing1' c hc).add_eq,
  simp_rw [← EQ1, ← p.add_eq] at hc,
  erw ← has_hadd.rel_h' at hc,
  exact hc,
end

lemma diagonal.from_balancing1_uniq
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k')
  (q' : diagonal a b c k') 
  (hq' : q'.2 = p.2) :
  p.from_balancing1 c hc = q' :=
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

lemma diagonal.from_balancing1_fst_eq {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k') :
  (p.from_balancing1 c hc).fst = a.next p.1 :=
begin 
  rw p.from_balancing1_uniq c hc(p.from_balancing1' c hc) rfl,
  refl,
end

@[simps]
def diagonal.from_balancing2
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k') :
  diagonal a b c k' :=
{ fst := p.1,
  snd := (has_hadd.balanced' p.1 p.2 k' (by rwa p.add_eq : c.rel (p.1+[a,b,c]p.2) k')).2.some,
  add_eq := begin 
    generalize_proofs h,
    exact h.some_spec.symm,
  end }


lemma diagonal.from_balancing2_uniq
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k') (q' : diagonal a b c k') 
  (hq' : q'.1 = p.1) :
  p.from_balancing2 c hc = q' :=
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
  {k k' : γ} (p : diagonal a b c k) (hc : c.rel k k') :
  diagonal a b c k' :=
{ fst := p.1,
  snd := b.next p.2,
  add_eq := begin 
    suffices : 
      (has_hadd.balanced' p.1 p.2 k' (by rwa p.add_eq : c.rel (p.1+[a,b,c]p.2) k')).2.some = 
      b.next p.2,
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
  (p.from_balancing2 c hc).snd = b.next p.2 :=
begin 
  rw p.from_balancing2_uniq c hc (p.from_balancing2' c hc) rfl,
  refl,
end

lemma has_sign.smul_sub [has_sign a] (i : α) 
  {T : Type*} [add_comm_group T] (t t' : T) :
  i • (t - t') = i • t - i • t' :=
begin 
  dunfold has_smul.smul,
  dsimp,
  split_ifs,
  { refl },
  abel,
end  

lemma has_sign.next_smul [has_sign a] (i : α) (ha : a.rel i (a.next i))
  {T : Type*} [add_comm_group T] (t : T) :
  a.next i • t = - (i • t) :=
begin 
  dunfold has_smul.smul,
  dsimp,
  have := has_sign.rel _ _ ha,
  split_ifs with h1 h2,
  { exfalso,
    rw [h1, h2] at this,
    exact this rfl, },
  { rw neg_neg },
  { refl, },
  { have h2' : has_sign.sign a i = 0 ∨ has_sign.sign a i = 1,
    { obtain hmm1 := (has_sign.sign a i).2,
      have hmm2 : 0 ≤ (has_sign.sign a i).1 := by linarith,
      interval_cases using hmm2 hmm1,
      left, ext, assumption,
      right, ext, assumption, },
    have h1' : has_sign.sign a (a.next i) = 0 ∨ has_sign.sign a (a.next i) = 1,
    { obtain hmm1 := (has_sign.sign a (a.next i)).2,
      have hmm2 : 0 ≤ (has_sign.sign a (a.next i)).1 := by linarith,
      interval_cases using hmm2 hmm1,
      left, ext, assumption,
      right, ext, assumption, },
    rw [h2'.resolve_left h, h1'.resolve_left h1] at this,
    exfalso,
    exact this rfl, }
end 

section
variables (a) (R)
lemma has_sign.smul_apply [has_sign a] (i : α) 
  {v₁ v₂ : Type*} [add_comm_group v₁] [add_comm_group v₂] [module R v₁] [module R v₂] 
  (f : v₁ →ₗ[R] v₂) (x)  :
  (i • f) x = i • (f x) :=
begin 
  dunfold has_smul.smul,
  dsimp,
  split_ifs,
  { refl },
  { rw linear_map.neg_apply, },
end
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

variable [∀ (k k' : γ), decidable $ c.rel k k']

@[reducible]
def total_d [has_sign a] (k k' : γ) :
  C.total_at c k ⟶ C.total_at c k' :=
if hc : c.rel k k' 
then direct_sum.to_module _ _ _ $ λ p, 
  (direct_sum.lof R _ _ (p.from_balancing1' c hc)).comp
    (C.d_v p.2 p.1 (a.next p.1)) +
  p.fst • (direct_sum.lof R _ _ (p.from_balancing2' c hc)).comp
    (C.d_h p.1 p.2 (b.next p.2))
else 0

lemma total_d_of_rel [has_sign a] (k k' : γ) (hc : c.rel k k') :
C.total_d c k k' = 
direct_sum.to_module _ _ _ (λ p, 
  (direct_sum.lof R _ _ (p.from_balancing1' c hc)).comp
    (C.d_v p.2 p.1 (a.next p.1)) +
  p.fst • (direct_sum.lof R _ _ (p.from_balancing2' c hc)).comp
    (C.d_h p.1 p.2 (b.next p.2))) :=
begin 
  dunfold total_d,
  apply direct_sum.linear_map_ext,
  intros p,
  ext1 x,
  rw dif_pos hc,
end

lemma total_d_comp_d_of_rel [has_sign a] (k₁ k₂ k₃ : γ) (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) :
  C.total_d c k₁ k₂ ≫ C.total_d c k₂ k₃ = 0 :=
begin 
  apply direct_sum.linear_map_ext,
  intros p,
  ext1 x,
  simp only [linear_map.comp_apply, comp_apply, linear_map.zero_apply],
  rw [total_d_of_rel, total_d_of_rel];
  try { assumption },
  simp only [direct_sum.to_module_lof, linear_map.add_apply, map_add, linear_map.comp_apply, 
    has_sign.map_smul, has_sign.smul_apply],
  rw [← comp_apply], erw [d_comp_d_v],
  erw has_sign.map_smul,
  simp only [direct_sum.to_module_lof, linear_map.comp_apply, linear_map.add_apply, 
    has_sign.smul_apply],
  nth_rewrite 2 [← comp_apply], erw [d_comp_d_h],
  simp only [linear_map.zero_apply, map_zero, has_sign.smul_zero, add_zero, zero_add],
  simp_rw show (diagonal.from_balancing1' c p hc12).fst = a.next p.fst, from rfl,
  have EQ : diagonal.from_balancing2' c (diagonal.from_balancing1' c p hc12) hc23 =
    diagonal.from_balancing1' c (diagonal.from_balancing2' c p hc12) hc23,
  { ext; dsimp; refl, },
  rw has_sign.next_smul,
  work_on_goal 2 { exact p.from_balancing1'_rel c hc12, },
  rw [neg_add_eq_sub, ← has_sign.smul_sub, has_sign.smul_eq_zero, sub_eq_zero],
  congr' 1,
  dsimp,
  rw [← comp_apply, ← comp_apply],
  rw C.comm,
end

@[simps]
def total_complex [has_sign a] : homological_complex (Module R) c :=
{ X := λ k, C.total_at c k,
  d := λ k k', C.total_d c k k',
  shape' := 
  begin 
    rintros, rw total_d, rw dif_neg, assumption
  end,
  d_comp_d' := 
  begin 
    intros,
    apply total_d_comp_d_of_rel;
    assumption
  end }

end defs_in_mod

end

end homological_bicomplex