import algebra.homology.homological_complex
import category_theory.abelian.exact
import algebra.category.Module.abelian

import tactic.interval_cases

import .test

noncomputable theory

universes v u

open category_theory category_theory.category category_theory.limits

variables {α β γ : Type}
variables (V : Type u) [category.{v} V] [preadditive V]

section defs

/--
A complex shape `a` on `α` is irreflexive if `i` is not relate to `i` for all `i : α`. 
-/
def complex_shape.irrefl (a : complex_shape α) : Prop :=
∀ (i : α), ¬ a.rel i i

lemma complex_shape.irrefl.ne {a : complex_shape α} (ha : a.irrefl) {i i' : α} :
  a.rel i i' → i ≠ i' :=
begin 
  contrapose!,
  rintro rfl,
  exact ha _,
end

/--
A complex shape `a` on `α` can be treated as having signs if any two related terms have different 
sign. 
-/
class has_sign (a : complex_shape α) :=
(sign : α → zmod 2)
(rel : ∀ (i i' : α), a.rel i i' → sign i ≠ sign i')

section has_sign

variables (a : complex_shape α) [has_sign a] {T : Type*} 

@[reducible]
def complex_shape.smul (i : α)  (f : T) [has_neg T] : T :=
if has_sign.sign a i = 0 then f else - f


@[simp] lemma has_sign.smul_zero [add_group T] (i : α) : a.smul i (0 : T) = 0 :=
begin
  dunfold complex_shape.smul,
  split_ifs,
  { refl },
  { rw neg_zero },
end

lemma has_sign.smul_comp (i : α) {x y z : V} (f : x ⟶ y) (g : y ⟶ z) :
  (a.smul i f) ≫ g = a.smul i (f ≫ g) :=
begin 
  dunfold complex_shape.smul,
  split_ifs,
  { refl },
  { rw preadditive.neg_comp },
end

lemma has_sign.comp_smul (i : α) {x y z : V} (f : x ⟶ y) (g : y ⟶ z) :
  f ≫ a.smul i g = a.smul i (f ≫ g) :=
begin 
  dunfold complex_shape.smul,
  split_ifs,
  { refl },
  { rw preadditive.comp_neg },
end

lemma has_sign.add_eq_zero_of_rel (i i' : α) (ha : a.rel i i') [add_group T] (x : T) :
  a.smul i x + a.smul i' x = 0 :=
begin 
  dunfold complex_shape.smul,
  split_ifs with h1 h2,
  { refine (has_sign.rel _ _ ha _).elim, rw [h1, h2], },
  { rw add_neg_eq_zero, },
  { rw neg_add_eq_zero, },
  { refine (has_sign.rel _ _ ha _).elim,
    have h1' : has_sign.sign a i = 1,
    { set x := (has_sign.sign a i), fin_cases x,
      { cases h1 this },
      { rw this, refl, }, },
    have h2' : has_sign.sign a i' = 1,
     { set x := (has_sign.sign a i'), fin_cases x,
      { cases h this },
      { rw this, refl, }, },
    rw [h1', h2'], },
end

lemma has_sign.smul_comp_linear_map (i : α) (R : Type*) [comm_ring R] (L M N : Type*)
  [add_comm_group L] [add_comm_group M] [add_comm_group N] [module R L] [module R M] [module R N] 
  (f : L →ₗ[R] M) (g : M →ₗ[R] N) :
  (a.smul i g).comp f = a.smul i (g.comp f) :=
begin 
  dunfold complex_shape.smul,
  split_ifs,
  { refl },
  { rw linear_map.neg_comp },
end

lemma has_sign.linear_map_comp_smul (i : α) (R : Type*) [comm_ring R] (L M N : Type*)
  [add_comm_group L] [add_comm_group M] [add_comm_group N] [module R L] [module R M] [module R N] 
  (f : L →ₗ[R] M) (g : M →ₗ[R] N) :
  g.comp (a.smul i f) = a.smul i (g.comp f) :=
begin 
  dunfold complex_shape.smul,
  split_ifs,
  { refl },
  { rw linear_map.comp_neg },
end

end has_sign

/--
Given three complex shapes `a` on `α`, `b` on `β` and `c` on `γ`, a heterogeneous addition 
`(+[a,b,c]) : α → β → γ` (written as `(+)` if `a, b, c` are clear from content) with respect to
the said complex shapes is such that:
* for all `j : β`, `i -> i'` according to `a` if and only if `i + j -> i' + j` according to `c`;
* for all `i : α`, `j -> j'` according to `b` if and only if `i + j -> i + j'` according to `c`;
* addition is cancellative, i.e. `i + j = i + j'` if and only if `i = j` and `i' + j = i' + j` 
  if and only if `j = j'`;
* it is possible to "squeeze" the middle term: if `i : α`, `j : β` and `k : γ` are three terms such
  that `(i + j) -> k` and `k -> (next i + next j)` according to `c`, then `k` is equal to both 
  `next i + j` and `i + next j`.
-/
class has_hadd (a : complex_shape α) (b : complex_shape β) (c : complex_shape γ):=
(add' {} : α → β → γ)
(rel_h' {} : ∀ (i₁ i₂ : α) (j : β), a.rel i₁ i₂ ↔ c.rel (add' i₁ j) (add' i₂ j))
(rel_v' {} : ∀ (i : α) (j₁ j₂ : β), b.rel j₁ j₂ ↔ c.rel (add' i j₁) (add' i j₂))
(add_cancel_h' : ∀ (i₁ i₂ : α) (j : β), add' i₁ j = add' i₂ j ↔ i₁ = i₂)
(add_cancel_v' : ∀ (i : α) (j₁ j₂ : β), add' i j₁ = add' i j₂ ↔ j₁ = j₂)
(squeeze' : ∀ (i : α) (j : β) (k : γ), c.rel (add' i j) k → c.rel k (add' (a.next i) (b.next j)) →
  (k = add' (a.next i) j ∧ k = add' i (b.next j)))

notation (name := hadd.add) i `+[` a, b, c`]` j := (has_hadd.add' a b c i j)

@[reducible]
def homological_bicomplex (a : complex_shape α) (b : complex_shape β) := 
  homological_complex (homological_complex V a) b

namespace homological_bicomplex

variables {V} {a : complex_shape α} {b : complex_shape β}

section general

variable (C : homological_bicomplex V a b)

@[reducible]
def obj (i : α) (j : β) : V :=
(C.X j).X i

@[reducible]
def d_v (j : β) (i i' : α) : C.obj i j ⟶ C.obj i' j :=
(C.X j).d i i' 

@[reducible]
def d_h (i : α) (j j' : β) : C.obj i j ⟶ C.obj i j' :=
(C.d j j').f i

@[simp] lemma d_comp_d_v (j : β) (i₁ i₂ i₃ : α) :
  C.d_v j i₁ i₂ ≫ C.d_v j i₂ i₃ = 0 := 
(C.X j).d_comp_d _ _ _

@[simp] lemma d_comp_d_h (i : α) (j₁ j₂ j₃ : β) :
  C.d_h i j₁ j₂ ≫ C.d_h i j₂ j₃ = 0 := 
by rw [← homological_complex.comp_f, C.d_comp_d, homological_complex.zero_apply]

@[simp] lemma comm (C : homological_bicomplex V a b) (j₁ j₂ : β) (i₁ i₂ : α) :
  C.d_h i₁ j₁ j₂ ≫ C.d_v j₂ i₁ i₂ = C.d_v j₁ i₁ i₂ ≫ C.d_h i₂ j₁ j₂ := 
homological_complex.hom.comm _ _ _

lemma shape_h (i : α) (j j' : β) (hb : ¬ b.rel j j') : C.d_h i j j' = 0 :=
by rwa [d_h, C.shape, homological_complex.zero_apply]

lemma shape_v (j : β) (i i' : α) (ha : ¬ a.rel i i') : C.d_v j i i' = 0 :=
(C.X j).shape _ _ ha

variables [decidable_eq α] [decidable_eq β] [decidable_eq γ] [has_sign b]
/--
A general differential for the bicomplex from `(i, j)` to `(i', j')` where it acts as the horizontal 
differential if `i = i'` and the vertical differential if `j = j'` and zero otherwise.
-/
def D (i₁ i₂ : α) (j₁ j₂ : β) :
  C.obj i₁ j₁ ⟶ C.obj i₂ j₂ :=
if H_h : i₁ = i₂ 
then C.d_h i₁ j₁ j₂ ≫ eq_to_hom (by rw H_h)
else if H_v : j₁ = j₂
  then b.smul j₁ (C.d_v j₁ i₁ i₂) ≫ eq_to_hom (by rw H_v)
  else 0

lemma D_eq_of_eq_h (i₁ i₂ : α) (j₁ j₂ : β)
  (h : i₁ = i₂) :
  C.D i₁ i₂ j₁ j₂ = C.d_h i₁ j₁ j₂ ≫ eq_to_hom (by rw h) :=
by rw [D, dif_pos h]  

lemma D_eq_of_eq_v (ha : a.irrefl) (hb : b.irrefl)
  (i₁ i₂ : α) (j₁ j₂ : β)
  (h : j₁ = j₂) :
  C.D i₁ i₂ j₁ j₂ = b.smul j₁ (C.d_v j₁ i₁ i₂) ≫ eq_to_hom (by rw h) :=
begin 
  rw [D],
  split_ifs with h1,
  { rw [C.shape_h, C.shape_v, zero_comp, has_sign.smul_zero, zero_comp],
    { substs h1 h, exact ha _, },
    { substs h1 h, exact hb _, }, },
  { refl, },
end

end general

section diagonal

variables (a b) (c : complex_shape γ) [has_hadd a b c]

/--
The diagonal of `k : γ` with respect to shapes `a`, `b` and `c` is pairs `(i, j) ∈ a × b` such that
`i +[a, b, c] j = k`.
-/
@[ext, nolint has_nonempty_instance]
structure diagonal (k : γ) :=
(fst : α) (snd : β) (add_eq : (fst +[a, b, c] snd) = k)

variables {a b}
/--
Considering `C_ij ⟶ C_mn`, only if `i = m` or `j = n` will `D` be potentially nonzero.
-/
@[reducible]
def diagonal.potentially_nonzero ⦃k : γ⦄ (p : diagonal a b c k) (k') : set (diagonal a b c k') :=
{p' | p'.1 = p.1} ∪ {p' | p'.2 = p.2}

lemma diagonal.subsingleton_of_fst_eq ⦃k : γ⦄ (p : diagonal a b c k) (k' : γ) :
  {p' : diagonal a b c k' | p'.1 = p.1}.subsingleton :=
begin 
  rintros ⟨x1, y1, eq1⟩ hx1 ⟨x2, y2, eq2⟩ hx2,
  dsimp at hx1 hx2,
  substs hx1 hx2,
  ext,
  { refl },
  { rw [← eq1, has_hadd.add_cancel_v'] at eq2,
    subst eq2, },
end

lemma diagonal.subsingleton_of_snd_eq ⦃k : γ⦄ (p : diagonal a b c k) (k' : γ) :
  {p' : diagonal a b c k' | p'.2 = p.2}.subsingleton :=
begin 
  rintros ⟨x1, y1, eq1⟩ hx1 ⟨x2, y2, eq2⟩ hx2,
  dsimp at hx1 hx2,
  substs hx1 hx2,
  ext,
  { rw [← eq1, has_hadd.add_cancel_h'] at eq2,
    subst eq2, },
  { refl },
end

lemma diagonal.potentially_nonzero_finite ⦃k : γ⦄ (p : diagonal a b c k) (k' : γ) :
  (p.potentially_nonzero c k').finite :=
begin
  refine set.finite.union (set.subsingleton.finite _) (set.subsingleton.finite _),
  { exact p.subsingleton_of_fst_eq c k' },
  { exact p.subsingleton_of_snd_eq c k' },
end


variables (k k' : γ)

lemma diagonal.subsingleton_of_fst_eq_and_snd_eq (i : α) (j : β) : 
  set.subsingleton {p : diagonal a b c k | p.1 = i ∧ p.2 = j} :=
begin 
  rintros ⟨i1, j1, h1⟩ ⟨rfl, rfl⟩ ⟨i2, j2, h2⟩ ⟨h21, h22⟩,
  dsimp at h21 h22,
  substs h21 h22,
end

instance diagonal.fintype_of_fst_eq_and_snd_eq (i : α) (j : β) :
  fintype {p : diagonal a b c k | p.1 = i ∧ p.2 = j} :=
begin 
  haveI : subsingleton {p : diagonal a b c k | p.fst = i ∧ p.snd = j},
  { fconstructor, 
    rintros ⟨p1, h1⟩ ⟨p2, h2⟩, 
    ext1,
    exact diagonal.subsingleton_of_fst_eq_and_snd_eq c k i j h1 h2, },
  exact fintype.of_finite _,
end

lemma diagonal.fixed_of_fst_eq (p : diagonal a b c k) (hc : c.rel k k') :
  {p' : diagonal a b c k' | p'.1 = p.1} =
  {p' : diagonal a b c k' | p'.1 = p.1 ∧ p'.2 = b.next p.2} := 
begin 
  rcases p with ⟨i, j, h⟩,
  ext1 ⟨i', j', h'⟩,
  dsimp,
  split,
  { rintro rfl,
    refine ⟨rfl, _⟩,
    rw [← h, ← h', ←has_hadd.rel_v'] at hc,
    exact (b.next_eq' hc).symm, },
  { rintro ⟨rfl, -⟩, refl, },
end

lemma diagonal.fixed_of_snd_eq (p : diagonal a b c k) (hc : c.rel k k') :
  {p' : diagonal a b c k' | p'.2 = p.2} =
  {p' : diagonal a b c k' | p'.1 = a.next p.1 ∧ p'.2 = p.2} := 
begin 
  rcases p with ⟨i, j, h⟩,
  ext1 ⟨i', j', h'⟩,
  dsimp,
  split,
  { rintro rfl,
    refine ⟨_, rfl⟩,
    rw [← h, ← h', ←has_hadd.rel_h'] at hc,
    exact (a.next_eq' hc).symm, },
  { rintro ⟨-, rfl⟩, refl, },
end

end diagonal

section Module


variables {R : Type u} [comm_ring R] (C : homological_bicomplex (Module.{v} R) a b)
variables (c : complex_shape γ) (k k' : γ) 

open_locale direct_sum big_operators

lemma direct_sum.to_module_comp (R : Type*) [comm_ring R] 
  {α β γ} [decidable_eq α] [decidable_eq β]
  (L : (α → Type*))  [∀ i , add_comm_monoid (L i)] [∀ i , module R (L i)]
  (M : (β → Type*))  [∀ i , add_comm_monoid (M i)] [∀ i , module R (M i)]
  (N : (γ → Type*))  [∀ i , add_comm_monoid (N i)] [∀ i , module R (N i)]
  (fLM : Π (a : α) , L a →ₗ[R] ⨁ j, M j)
  (fMN : Π (b : β), M b →ₗ[R] ⨁ k, N k)
  (fLN : Π (a : α) , L a →ₗ[R] ⨁ k, N k)
  (H : ∀ (i : α), (direct_sum.to_module _ _ _ fMN).comp (fLM i) = fLN i) :
  (direct_sum.to_module _ _ _ fMN : 
      (⨁ i, M i) →ₗ[R] (⨁ i, N i)).comp 
    (direct_sum.to_module _ _ _ fLM : 
      (⨁ i, L i) →ₗ[R] (⨁ i, M i)) = 
  direct_sum.to_module _ _ _ fLN :=
begin 
  classical,
  apply direct_sum.linear_map_ext,
  intros i,
  ext1 y,
  simp only [linear_map.comp_apply, direct_sum.to_module_lof],
  specialize H i,
  rw ← H,
  refl,
end

section total

variables {a b} [has_hadd a b c]
/--
The total complex at `k`-th position is `⨁_{i + j = k} C_ij`.
-/
@[reducible]
def total_obj (j : γ) : Module R :=
Module.of.{v} R $ ⨁ (p : diagonal a b c j), C.obj p.fst p.snd

/--
The map `C_mn ⟶ ⨁_{i + j = k} C_ij` where `m + n = k`
-/
@[reducible]
def emb_total_obj (k : γ) (p : diagonal a b c k) [∀ k, decidable_eq $ diagonal a b c k] :
  C.obj p.fst p.snd →ₗ[R] C.total_obj c k :=
direct_sum.lof R _ _ p

lemma emb_total_obj_comp_congr (k : γ) (p p' : diagonal a b c k) (EQ : p = p') (M : Module.{v} R)
  (f : Π (p : diagonal a b c k), (M →ₗ[R] C.obj p.1 p.2)) [∀ k, decidable_eq $ diagonal a b c k] :
  (C.emb_total_obj c k p).comp (f p) = 
  (C.emb_total_obj c k p').comp (f p') := 
begin 
  rcases ⟨p, p'⟩ with ⟨⟨i, j, h⟩, ⟨i', j', h'⟩⟩,
  rw diagonal.ext_iff at EQ,
  dsimp only at EQ,
  cases EQ with EQ1 EQ2,
  substs EQ1 EQ2,
end

variables [decidable_eq α] [decidable_eq β] [has_sign b]

/--
`⨁_{i + j = k} C_ij ⟶ ⨁_{i + j = k'} C_ij` is defined to be the linear map whose `(i, j)`-th
projection `C_ij ⟶ ⨁_{m + n = k'} C_mn` is defined to be the sum of all `C_ij ⟶ C_mn ⟶ ⨁`.
-/
@[reducible]
def total_d [∀ k, decidable_eq $ diagonal a b c k] : C.total_obj c k ⟶ C.total_obj c k' :=
direct_sum.to_module R _ _ $ λ p, 
  ∑ (p' : diagonal a b c k') in (p.potentially_nonzero_finite c k').to_finset, 
    (C.emb_total_obj c k' p').comp (C.D p.1 p'.1 p.2 p'.2)

instance t1 {k k'} (p : diagonal a b c k) : fintype {p' : diagonal a b c k' | p'.fst = p.fst} := 
(p.subsingleton_of_fst_eq c k').finite.fintype

instance t2 {k k'} (p : diagonal a b c k) : fintype {p' : diagonal a b c k' | p'.snd = p.snd} := 
(p.subsingleton_of_snd_eq c k').finite.fintype

lemma sum_potentially_nonzero_finite_eq_union (c_ir : c.irrefl) (hc : c.rel k k') 
  {M : Type*} [add_comm_monoid M]
  (p : diagonal a b c k) (f : diagonal a b c k' → M) :
  ∑ (p' : diagonal a b c k') in (p.potentially_nonzero_finite c k').to_finset, f p' = 
  (∑ p' in {p' : diagonal a b c k' | p'.fst = p.fst}.to_finset, f p') +
  (∑ p' in {p' : diagonal a b c k' | p'.snd = p.snd}.to_finset, f p') := 
begin
  classical,
  haveI : fintype {p' : diagonal a b c k' | p'.fst = p.fst},
  { exact (p.subsingleton_of_fst_eq c k').finite.fintype, },
  haveI : fintype {p' : diagonal a b c k' | p'.snd = p.snd},
  { exact (p.subsingleton_of_snd_eq c k').finite.fintype, },

  transitivity ∑ (p' : diagonal a b c k') in 
    ({p' | p'.1 = p.1} : set (diagonal a b c k')).to_finset ∪ {p' : diagonal a b c k' | p'.2 = p.2}.to_finset, 
    f p',
  { refine finset.sum_congr _ (λ _ _, rfl),
    ext1, simp only [set.finite.mem_to_finset, set.mem_union, finset.mem_union, set.mem_to_finset], },
  transitivity ∑ (p' : diagonal a b c k') in
    ({p' | p'.1 = p.1} : set (diagonal a b c k')).to_finset.disj_union 
      ({p' : diagonal a b c k' | p'.2 = p.2}.to_finset) _, f p',
  work_on_goal 2 {
    rw finset.disjoint_iff_ne,
    rintros ⟨i1, j1, h1⟩ hi1 ⟨i2, j2, h2⟩ hi2 H,
    simp only [set.mem_to_finset, set.mem_set_of_eq] at hi1 hi2,
    rw [diagonal.ext_iff] at H,
    dsimp only at H,
    rcases H with ⟨H1, H2⟩,
    substs H1 H2,
    rw [hi1, hi2, p.add_eq] at h1,
    exact c_ir.ne hc h1,
  },
  { refine finset.sum_congr _ (λ _ _, rfl),
    exact (finset.disj_union_eq_union _ _ _).symm, },
  rw finset.sum_disj_union,
  congr,
end

lemma total_d_comp_d_eq_double_sum (k₁ k₂ k₃ : γ) [∀ k, decidable_eq $ diagonal a b c k] : 
  (C.total_d c k₂ k₃).comp (C.total_d c k₁ k₂) = 
  direct_sum.to_module _ _ _ (λ p₁, 
    ∑ (p₂ : diagonal a b c k₂) in (p₁.potentially_nonzero_finite c k₂).to_finset,
      ∑ (p₃ : diagonal a b c k₃) in (p₂.potentially_nonzero_finite c k₃).to_finset,
        (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2))) :=
begin
  rw [total_d, total_d],
  refine direct_sum.to_module_comp R _ _ _ _ _ _ _,
  intros p₁,
  rw [linear_map.comp_sum],
  refine finset.sum_congr rfl _,
  intros p₂ hp₂,
  simp only [set.finite.mem_to_finset, set.mem_union, set.mem_set_of_eq] at hp₂,
  ext1 x,
  simp only [linear_map.comp_apply, direct_sum.to_module_lof, linear_map.sum_apply],
end

lemma total_d_comp_d_eq_4_sums (k₁ k₂ k₃ : γ) (c_ir : c.irrefl)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) [∀ k, decidable_eq $ diagonal a b c k] : 
  (C.total_d c k₂ k₃).comp (C.total_d c k₁ k₂) = 
  direct_sum.to_module _ _ _ (λ p₁, 
    (∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst}.to_finset,
      ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = p₂.fst}.to_finset,
        (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2))) +
    (∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst}.to_finset,
      ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.snd = p₂.snd}.to_finset,
        (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2))) +
    (∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.snd = p₁.snd}.to_finset,
      ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = p₂.fst}.to_finset,
        (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2))) +
    (∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.snd = p₁.snd}.to_finset,
      ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.snd = p₂.snd}.to_finset,
        (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)))) :=
begin
  classical,
  rw C.total_d_comp_d_eq_double_sum,
  ext p₁ x : 2,
  simp only [direct_sum.to_module_lof, linear_map.comp_apply, linear_map.sum_apply, 
    linear_map.zero_apply, direct_sum.zero_apply],
  rw sum_potentially_nonzero_finite_eq_union c k₁ k₂ c_ir hc12 p₁ _,
  simp only [linear_map.add_apply, linear_map.sum_apply],
  rw [add_assoc],
  refine congr_arg2 (+) _ _,
  { rw [← finset.sum_add_distrib],
    refine finset.sum_congr rfl _,
    intros p₂ hp₂,
    rw sum_potentially_nonzero_finite_eq_union c k₂ k₃ c_ir hc23 p₂ _,
    refl,  },
  { rw [← finset.sum_add_distrib],
    refine finset.sum_congr rfl _,
    intros p₂ hp₂,
    rw sum_potentially_nonzero_finite_eq_union c k₂ k₃ c_ir hc23 p₂ _,
    refl, },
end

lemma total_d_comp_d_eq_4_sums.fourth_zero (k₁ k₂ k₃ : γ) 
  (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) (p₁ : diagonal a b c k₁) 
  [∀ k, decidable_eq $ diagonal a b c k] :
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.snd = p₁.snd}.to_finset,
      ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.snd = p₂.snd}.to_finset,
        (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) = 0 := 
begin 
  apply finset.sum_eq_zero,
  intros p₂ hp₂,
  apply finset.sum_eq_zero,
  intros p₃ hp₃,
  simp only [set.mem_to_finset, set.mem_set_of_eq] at hp₂ hp₃,
  suffices :  C.D p₁.fst p₂.fst p₁.snd p₂.snd ≫ C.D p₂.fst p₃.fst p₂.snd p₃.snd = 0,
  { change linear_map.comp _ _ = 0 at this,
    rw [this, linear_map.comp_zero], },
  
  rcases ⟨p₁, p₂, p₃⟩ with ⟨⟨i₁, j₁, h₁⟩, ⟨i₂, j₂, h₂⟩, ⟨i₃, j₃, h₃⟩⟩,
  dsimp at *,
  substs hp₂ hp₃,
  rw [C.D_eq_of_eq_v a_ir b_ir _ _ _ _ rfl, C.D_eq_of_eq_v a_ir b_ir _ _ _ _ rfl, eq_to_hom_refl,
    eq_to_hom_refl, comp_id, comp_id, has_sign.smul_comp, has_sign.comp_smul, d_comp_d_v,
    has_sign.smul_zero, has_sign.smul_zero],
end

lemma total_d_comp_d_eq_4_sums.fst_zero (k₁ k₂ k₃ : γ) (p₁ : diagonal a b c k₁) 
  (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl)
  [∀ k, decidable_eq $ diagonal a b c k] :
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = p₂.fst}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) = 0 := 
begin 
  apply finset.sum_eq_zero,
  intros p₂ hp₂,
  apply finset.sum_eq_zero,
  intros p₃ hp₃,
  simp only [set.mem_to_finset, set.mem_set_of_eq] at hp₂ hp₃,
  suffices :  C.D p₁.fst p₂.fst p₁.snd p₂.snd ≫ C.D p₂.fst p₃.fst p₂.snd p₃.snd = 0,
  { change linear_map.comp _ _ = 0 at this,
    rw [this, linear_map.comp_zero], },
  rcases ⟨p₁, p₂, p₃⟩ with ⟨⟨i₁, j₁, h₁⟩, ⟨i₂, j₂, h₂⟩, ⟨i₃, j₃, h₃⟩⟩,
  dsimp at *,
  substs hp₂ hp₃,
  rw [C.D_eq_of_eq_h, C.D_eq_of_eq_h, eq_to_hom_refl, eq_to_hom_refl, comp_id, comp_id, d_comp_d_h];
  assumption <|> refl,
end

lemma total_d_comp_d_eq_2_sums (k₁ k₂ k₃ : γ) 
  (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) [∀ k, decidable_eq $ diagonal a b c k] : 
  (C.total_d c k₂ k₃).comp (C.total_d c k₁ k₂) = 
  direct_sum.to_module _ _ _ (λ p₁, 
    (∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst}.to_finset,
      ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.snd = p₂.snd}.to_finset,
        (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2))) +
    (∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.snd = p₁.snd}.to_finset,
      ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = p₂.fst}.to_finset,
        (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)))) :=
begin
  classical,
  rw total_d_comp_d_eq_4_sums C c _ _ _ c_ir hc12 hc23,
  congr' 1,
  ext p₁ : 1,
  rw total_d_comp_d_eq_4_sums.fst_zero;
  try { assumption },
  rw [zero_add, total_d_comp_d_eq_4_sums.fourth_zero];
  try { assumption },
  rw [add_zero],
end

lemma total_d_comp_d_eq_2_sums.fst_eq1 (k₁ k₂ k₃ : γ)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) (p₁ : diagonal a b c k₁) 
  [∀ k, decidable_eq $ diagonal a b c k] : 
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.snd = p₂.snd}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) =
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) := 
begin 
  classical,
  refine finset.sum_congr _ (λ p₂ hp₂, finset.sum_congr _ (λ _ _, rfl)),
  { rw set.to_finset_inj,
    rw diagonal.fixed_of_fst_eq,
    assumption, },
  { rw set.to_finset_inj,
    rw diagonal.fixed_of_snd_eq,
    work_on_goal 2 { assumption, },
    simp only [set.mem_to_finset, set.mem_set_of_eq] at hp₂,
    rw [hp₂.1, hp₂.2], }
end

lemma total_d_comp_d_eq_2_sums.snd_eq1 (k₁ k₂ k₃ : γ)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) (p₁ : diagonal a b c k₁) 
  [∀ k, decidable_eq $ diagonal a b c k] : 
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.snd = p₁.snd}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = p₂.fst}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) =
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = a.next p₁.fst ∧ p'.snd = p₁.snd}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) := 
begin 
  classical,
  refine finset.sum_congr _ (λ p₂ hp₂, finset.sum_congr _ (λ _ _, rfl)),
  { rw set.to_finset_inj,
    rw diagonal.fixed_of_snd_eq,
    assumption, },
  { rw set.to_finset_inj,
    rw diagonal.fixed_of_fst_eq,
    work_on_goal 2 { assumption, },
    simp only [set.mem_to_finset, set.mem_set_of_eq] at hp₂,
    rw [hp₂.1, hp₂.2], }
end

lemma total_d_comp_d_eq_2_sums.fst_eq2 (k₁ k₂ k₃ : γ)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) (p₁ : diagonal a b c k₁) 
  [∀ k, decidable_eq $ diagonal a b c k] : 
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.snd = p₂.snd}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) =
  ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset,
    ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) := 
begin 
  rw total_d_comp_d_eq_2_sums.fst_eq1;
  try { assumption },
  exact finset.sum_comm,
end


lemma total_d_comp_d_eq_2_sums.snd_eq2 (k₁ k₂ k₃ : γ)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) (p₁ : diagonal a b c k₁) 
  [∀ k, decidable_eq $ diagonal a b c k] : 
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.snd = p₁.snd}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = p₂.fst}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) =
  ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset,
    ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = a.next p₁.fst ∧ p'.snd = p₁.snd}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) := 
begin 
  rw total_d_comp_d_eq_2_sums.snd_eq1;
  try { assumption },
  exact finset.sum_comm,
end

lemma total_d_comp_d_eq_2_sums.fst_eq3 (k₁ k₂ k₃ : γ)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) (p₁ : diagonal a b c k₁) 
  [∀ k, decidable_eq $ diagonal a b c k] : 
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.snd = p₂.snd}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) =
  ∑ p₃ in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset.attach,
    ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset,
      (C.emb_total_obj c _ ⟨a.next p₁.fst, b.next p₁.snd, begin 
        have h3 := p₃.2, simp only [set.mem_to_finset, set.mem_set_of_eq] at h3,
        rw [←h3.1], simp_rw [←h3.2], exact p₃.1.add_eq,
      end⟩).comp ((C.D p₂.1 (a.next p₁.1) p₂.2 (b.next p₁.2)).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) := 
begin 
  rw total_d_comp_d_eq_2_sums.fst_eq2;
  try { assumption },
  rw ← finset.sum_attach,
  refine finset.sum_congr rfl _,
  rintros ⟨p₃, hp3⟩ -,
  refine finset.sum_congr rfl _,
  rintros p₂ hp2,
  simp only [set.mem_to_finset, set.mem_set_of_eq, finset.mem_attach] at hp3 hp2,
  rw [subtype.coe_mk],
  apply emb_total_obj_comp_congr,
  ext, 
  { exact hp3.1 }, 
  { exact hp3.2 }
end


lemma total_d_comp_d_eq_2_sums.snd_eq3 (k₁ k₂ k₃ : γ)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) (p₁ : diagonal a b c k₁) 
  [∀ k, decidable_eq $ diagonal a b c k] : 
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.snd = p₁.snd}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = p₂.fst}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) =
  ∑ p₃ in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset.attach,
    ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = a.next p₁.fst ∧ p'.snd = p₁.snd}.to_finset,
      (C.emb_total_obj c _ ⟨a.next p₁.1, b.next p₁.2, begin 
        have h3 := p₃.2, simp only [set.mem_to_finset, set.mem_set_of_eq] at h3,
        rw [←h3.1], simp_rw [←h3.2], exact p₃.1.add_eq,
      end⟩).comp ((C.D p₂.1 (a.next p₁.1) p₂.2 (b.next p₁.2)).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) := 
begin 
  rw total_d_comp_d_eq_2_sums.snd_eq2;
  try { assumption },
  rw ← finset.sum_attach,
  refine finset.sum_congr rfl _,
  rintros ⟨p₃, hp3⟩ -,
  refine finset.sum_congr rfl _,
  rintros p₂ hp2,
  simp only [set.mem_to_finset, set.mem_set_of_eq, finset.mem_attach] at hp3 hp2,
  rw [subtype.coe_mk],
  apply emb_total_obj_comp_congr,
  ext, 
  { exact hp3.1 }, 
  { exact hp3.2 }
end

lemma total_d_comp_d_eq_2_sums.fst_eq4 (k₁ k₂ k₃ : γ)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) (p₁ : diagonal a b c k₁) 
  [∀ k, decidable_eq $ diagonal a b c k] : 
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.fst = p₁.fst}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.snd = p₂.snd}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) =
  ∑ p₃ in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset.attach,
    (C.emb_total_obj c _ ⟨a.next p₁.fst, b.next p₁.snd, begin 
      have h3 := p₃.2, simp only [set.mem_to_finset, set.mem_set_of_eq] at h3,
      rw [←h3.1], simp_rw [←h3.2], exact p₃.1.add_eq,
    end⟩).comp ((C.D p₁.1 (a.next p₁.1) (b.next p₁.2) (b.next p₁.2)).comp (C.D p₁.1 p₁.1 p₁.2 (b.next p₁.2))) := 
begin
  rw total_d_comp_d_eq_2_sums.fst_eq3;
  try { assumption },
  refine finset.sum_congr rfl _,
  rintros ⟨p₃, hp3⟩ -,
  simp only [set.mem_to_finset, set.mem_set_of_eq] at hp3,
  have add_eq1 : (p₁.fst+[a,b,c]b.next p₁.snd) = k₂,
  { have add_eq3 := p₃.add_eq,
    rw [hp3.1, hp3.2] at add_eq3,
    rw ← add_eq3 at hc23,
    rw ← p₁.add_eq at hc12, 
    exact (has_hadd.squeeze' _ _ _ hc12 hc23).2.symm,
  },
  have EQ : {p' : diagonal a b c k₂ | p'.fst = p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset =
    {⟨p₁.1, b.next p₁.2, add_eq1⟩},
  { ext1 p₂,
    simp only [set.mem_to_finset, set.mem_set_of_eq, finset.mem_singleton],
    split,
    { rintros ⟨h1, h2⟩, simp_rw [←h1, ←h2], ext, { refl, }, { refl, } },
    { intros h, rw diagonal.ext_iff at h, exact ⟨h.1, h.2⟩, }, },
  rw [EQ, finset.sum_singleton],
end

lemma total_d_comp_d_eq_2_sums.snd_eq4 (k₁ k₂ k₃ : γ)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) (p₁ : diagonal a b c k₁) 
  [∀ k, decidable_eq $ diagonal a b c k] : 
  ∑ (p₂ : diagonal a b c k₂) in {p' : diagonal a b c k₂ | p'.snd = p₁.snd}.to_finset,
    ∑ (p₃ : diagonal a b c k₃) in {p' : diagonal a b c k₃ | p'.fst = p₂.fst}.to_finset,
      (C.emb_total_obj c _ p₃).comp ((C.D p₂.1 p₃.1 p₂.2 p₃.2).comp (C.D p₁.1 p₂.1 p₁.2 p₂.2)) =
  ∑ p₃ in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset.attach,
    (C.emb_total_obj c _ ⟨a.next p₁.1, b.next p₁.2, begin 
      have h3 := p₃.2, simp only [set.mem_to_finset, set.mem_set_of_eq] at h3,
      rw [←h3.1], simp_rw [←h3.2], exact p₃.1.add_eq,
    end⟩).comp ((C.D (a.next p₁.1) (a.next p₁.1) p₁.2 (b.next p₁.2)).comp (C.D p₁.1 (a.next p₁.1) p₁.2 p₁.2)) := 
begin
  rw total_d_comp_d_eq_2_sums.snd_eq3;
  try { assumption },
  refine finset.sum_congr rfl _,
  rintros ⟨p₃, hp3⟩ -,
  simp only [set.mem_to_finset, set.mem_set_of_eq] at hp3,
  have add_eq1 : (a.next p₁.fst +[a,b,c] p₁.snd) = k₂,
  { have add_eq3 := p₃.add_eq,
    rw [hp3.1, hp3.2] at add_eq3,
    rw ← add_eq3 at hc23,
    rw ← p₁.add_eq at hc12, 
    exact (has_hadd.squeeze' _ _ _ hc12 hc23).1.symm,
  },
  have EQ : {p' : diagonal a b c k₂ | p'.fst = a.next p₁.fst ∧ p'.snd = p₁.snd}.to_finset =
    {⟨a.next p₁.1, p₁.2, add_eq1⟩},
  { ext1 p₂,
    simp only [set.mem_to_finset, set.mem_set_of_eq, finset.mem_singleton],
    split,
    { rintros ⟨h1, h2⟩, simp_rw [←h1, ←h2], ext, { refl, }, { refl, } },
    { intros h, rw diagonal.ext_iff at h, exact ⟨h.1, h.2⟩, }, },
  rw [EQ, finset.sum_singleton],
end

lemma total_d_comp_d_eq_2_sums' (k₁ k₂ k₃ : γ)
  (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) [∀ k, decidable_eq $ diagonal a b c k] : 
  (C.total_d c k₂ k₃).comp (C.total_d c k₁ k₂) = 
  direct_sum.to_module _ _ _ (λ p₁, 
    (∑ p₃ in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset.attach,
      (C.emb_total_obj c _ ⟨a.next p₁.fst, b.next p₁.snd, begin 
        have h3 := p₃.2, simp only [set.mem_to_finset, set.mem_set_of_eq] at h3,
        rw [←h3.1], simp_rw [←h3.2], exact p₃.1.add_eq,
      end⟩).comp ((C.D p₁.1 (a.next p₁.1) (b.next p₁.2) (b.next p₁.2)).comp (C.D p₁.1 p₁.1 p₁.2 (b.next p₁.2)))) +
    (∑ p₃ in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset.attach,
      (C.emb_total_obj c _ ⟨a.next p₁.1, b.next p₁.2, begin 
        have h3 := p₃.2, simp only [set.mem_to_finset, set.mem_set_of_eq] at h3,
        rw [←h3.1], simp_rw [←h3.2], exact p₃.1.add_eq,
      end⟩).comp ((C.D (a.next p₁.1) (a.next p₁.1) p₁.2 (b.next p₁.2)).comp (C.D p₁.1 (a.next p₁.1) p₁.2 p₁.2)))) :=
begin 
  rw total_d_comp_d_eq_2_sums;
  try { assumption },
  congr' 1,
  ext p₁ : 1,
  congr' 1,
  { rw [total_d_comp_d_eq_2_sums.fst_eq4];
    assumption },
  { rw [total_d_comp_d_eq_2_sums.snd_eq4];
    assumption },
  all_goals { assumption },
end


lemma total_d_comp_d_eq_single_sum (k₁ k₂ k₃ : γ) 
  (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) [∀ k, decidable_eq $ diagonal a b c k] : 
  (C.total_d c k₂ k₃).comp (C.total_d c k₁ k₂) = 
  direct_sum.to_module _ _ _ (λ p₁, 
    (∑ p₃ in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset.attach,
      ((C.emb_total_obj c _ ⟨a.next p₁.fst, b.next p₁.snd, begin 
        have h3 := p₃.2, simp only [set.mem_to_finset, set.mem_set_of_eq] at h3,
        rw [←h3.1], simp_rw [←h3.2], exact p₃.1.add_eq,
      end⟩).comp ((C.D p₁.1 (a.next p₁.1) (b.next p₁.2) (b.next p₁.2)).comp (C.D p₁.1 p₁.1 p₁.2 (b.next p₁.2))) +
      (C.emb_total_obj c _ ⟨a.next p₁.1, b.next p₁.2, begin 
          have h3 := p₃.2, simp only [set.mem_to_finset, set.mem_set_of_eq] at h3,
          rw [←h3.1], simp_rw [←h3.2], exact p₃.1.add_eq,
        end⟩).comp ((C.D (a.next p₁.1) (a.next p₁.1) p₁.2 (b.next p₁.2)).comp (C.D p₁.1 (a.next p₁.1) p₁.2 p₁.2))))) :=
begin 
  rw total_d_comp_d_eq_2_sums';
  try { assumption },
  congr' 1,
  ext1 p₁,
  rw finset.sum_add_distrib,
end


lemma total_d_comp_d_eq_single_sum' (k₁ k₂ k₃ : γ)
  (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) [∀ k, decidable_eq $ diagonal a b c k] : 
  (C.total_d c k₂ k₃).comp (C.total_d c k₁ k₂) = 
  direct_sum.to_module _ _ _ (λ p₁, 
    (∑ p₃ in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset.attach,
      ((C.emb_total_obj c _ ⟨a.next p₁.fst, b.next p₁.snd, begin 
        have h3 := p₃.2, simp only [set.mem_to_finset, set.mem_set_of_eq] at h3,
        rw [←h3.1], simp_rw [←h3.2], exact p₃.1.add_eq,
      end⟩).comp 
        (((C.D p₁.1 (a.next p₁.1) (b.next p₁.2) (b.next p₁.2)).comp (C.D p₁.1 p₁.1 p₁.2 (b.next p₁.2))) + 
         ((C.D (a.next p₁.1) (a.next p₁.1) p₁.2 (b.next p₁.2)).comp (C.D p₁.1 (a.next p₁.1) p₁.2 p₁.2)))))) :=
begin 
  rw total_d_comp_d_eq_single_sum;
  try { assumption },
  congr' 1,
  ext1 p₁,
  refine finset.sum_congr rfl _,
  rintros ⟨p₂, hp2⟩ -,
  rw linear_map.comp_add,
end


lemma total_d_comp_d_eq_single_sum'' (k₁ k₂ k₃ : γ)
  (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) [∀ k, decidable_eq $ diagonal a b c k] : 
  (C.total_d c k₂ k₃).comp (C.total_d c k₁ k₂) = 
  direct_sum.to_module _ _ _ (λ p₁, 
    (∑ p₃ in {p' : diagonal a b c k₃ | p'.fst = a.next p₁.fst ∧ p'.snd = b.next p₁.snd}.to_finset.attach,
      ((C.emb_total_obj c _ ⟨a.next p₁.fst, b.next p₁.snd, begin 
        have h3 := p₃.2, simp only [set.mem_to_finset, set.mem_set_of_eq] at h3,
        rw [←h3.1], simp_rw [←h3.2], exact p₃.1.add_eq,
      end⟩).comp 
        (((b.smul (b.next p₁.2) (C.d_v (b.next p₁.2) p₁.1 (a.next p₁.1))).comp (C.d_h p₁.1 p₁.2 (b.next p₁.2))) + 
         ((C.d_h (a.next p₁.1) p₁.2 (b.next p₁.2)).comp (b.smul p₁.2 (C.d_v p₁.2 p₁.1 (a.next p₁.1)))))))) :=
begin 
  rw total_d_comp_d_eq_single_sum';
  try { assumption },
  congr' 1,
  ext1 p₁,
  refine finset.sum_congr rfl _,
  rintros ⟨p₂, hp2⟩ -,
  simp only [set.mem_to_finset, set.mem_set_of_eq] at hp2,
  have hc12' := hc12,
  have hc23' := hc23,
  rw [← p₂.add_eq, hp2.1, hp2.2] at hc23,
  rw [← p₁.add_eq] at hc12,
  have hk2 := has_hadd.squeeze' _ _ _ hc12 hc23,
  have h1 : p₁.fst ≠ a.next p₁.fst,
  { intro rid,
    rw [← rid] at hk2,
    suffices : k₂ = k₁,
    { rw this at hc12',
      refine c_ir.ne hc12' rfl, },
    rw [hk2.1, p₁.add_eq], },
  dunfold D,
  rw [dif_neg h1, dif_pos rfl, eq_to_hom_refl, comp_id, dif_pos rfl, eq_to_hom_refl, comp_id,
    dif_pos rfl, eq_to_hom_refl, comp_id, dif_neg h1, has_sign.smul_comp_linear_map,
    dif_pos rfl, eq_to_hom_refl, comp_id, has_sign.linear_map_comp_smul],
end


lemma total_d_comp_d_eq_0' (k₁ k₂ k₃ : γ) 
  (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) [∀ k, decidable_eq $ diagonal a b c k] : 
  (C.total_d c k₂ k₃).comp (C.total_d c k₁ k₂) = 
  direct_sum.to_module _ _ _ (λ p₁, 0) :=
begin 
  rw total_d_comp_d_eq_single_sum'';
  try { assumption },
  apply congr_arg _ _,
  -- congr' 1,
  ext p₁ : 1,
  refine finset.sum_eq_zero _,
  rintros ⟨p₃, hp3⟩ -,
  suffices : (_ + _ : _ →ₗ[R] _) = 0,
  { rw [this, linear_map.comp_zero], },
  rw [has_sign.smul_comp_linear_map, has_sign.linear_map_comp_smul],
  change b.smul _ (C.d_h p₁.fst p₁.snd (b.next p₁.snd) ≫ C.d_v (b.next p₁.snd) p₁.fst (a.next p₁.fst)) + _ = 0,
  rw C.comm,
  change b.smul _ (linear_map.comp _ _) + _ = _,
  rw add_comm,
  apply has_sign.add_eq_zero_of_rel,

  have hc12' := hc12,
  have hc23' := hc23,
  simp only [set.mem_to_finset, set.mem_set_of_eq] at hp3,
  rw [← p₃.add_eq, hp3.1, hp3.2] at hc23,
  rw [← p₁.add_eq] at hc12,
  have hk2 := has_hadd.squeeze' _ _ _ hc12 hc23,
  rwa [hk2.2, ← has_hadd.rel_v'] at hc12,
end


lemma total_d_comp_d' (k₁ k₂ k₃ : γ) 
  (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) [∀ k, decidable_eq $ diagonal a b c k] : 
  (C.total_d c k₂ k₃).comp (C.total_d c k₁ k₂) = 0 :=
begin 
  rw total_d_comp_d_eq_0';
  try { assumption },
  apply direct_sum.linear_map_ext,
  intros p₁,
  rw [linear_map.zero_comp],
  ext1 x,
  simp only [linear_map.comp_apply, linear_map.zero_apply, direct_sum.to_module_lof],
end

lemma total_d_comp_d (k₁ k₂ k₃ : γ)
  (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl)
  (hc12 : c.rel k₁ k₂) (hc23 : c.rel k₂ k₃) [∀ k, decidable_eq $ diagonal a b c k] : 
  (C.total_d c k₁ k₂) ≫ (C.total_d c k₂ k₃) = 0 :=
C.total_d_comp_d' c k₁ k₂ k₃ a_ir b_ir c_ir hc12 hc23

lemma total_d_shape' (a_ir : a.irrefl) (b_ir : b.irrefl) (hc : ¬ c.rel k k') [Π (k : γ), decidable_eq (diagonal a b c k)] : 
  C.total_d c k k' = 0 :=
begin 
  rw [total_d],
  apply direct_sum.linear_map_ext,
  intros p,
  ext1 x,
  simp only [linear_map.comp_apply, linear_map.zero_apply, direct_sum.to_module_lof, 
    linear_map.zero_comp, linear_map.sum_apply],
  refine finset.sum_eq_zero (λ p' hp', _),
  simp only [set.finite.mem_to_finset, set.mem_union, set.mem_set_of_eq] at hp',
  suffices : C.D p.fst p'.fst p.snd p'.snd = 0,
  { rw [this, linear_map.zero_apply, map_zero] },
  rcases hp' with (hp'|hp'),
  { rw [D, dif_pos hp'.symm, C.shape_h, zero_comp],
    contrapose! hc,
    rwa [← p.add_eq, ← p'.add_eq, hp', ← has_hadd.rel_v'], },
  { rw [D_eq_of_eq_v C a_ir b_ir _ _ _ _ hp'.symm, C.shape_v, has_sign.smul_zero, zero_comp],
    { contrapose! hc,
      rwa [← p.add_eq, ← p'.add_eq, hp', ← has_hadd.rel_h'], }, },
end

/--
The total complex associated with a double complex by taking direct sums.
-/
@[simps]
def total_complex (a_ir : a.irrefl) (b_ir : b.irrefl) (c_ir : c.irrefl) 
  [Π (k : γ), decidable_eq (diagonal a b c k)] : 
  homological_complex (Module R) c :=
{ X := C.total_obj c,
  d := λ i j, C.total_d c i j,
  shape' := λ i j hc, C.total_d_shape' c i j a_ir b_ir hc,
  d_comp_d' := λ i j k h1 h2, C.total_d_comp_d c i j k a_ir b_ir c_ir h1 h2 }

end total

end Module

end homological_bicomplex

end defs
