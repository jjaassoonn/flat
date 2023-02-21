import category_theory.abelian.exact
import category_theory.limits.exact_functor
import algebra.homology.exact

universes u v

open category_theory.limits

namespace category_theory

variables (C D : Type u) [category.{v} C] [category.{v} D] 
variables [abelian C] [abelian D]

open_locale zero_object

@[ext] structure pre_ses :=
(left middle right : C)
(lm : left ⟶ middle)
(mr : middle ⟶ right)

@[ext] structure pre_ses.morphism (s t : pre_ses C) :=
(vl : s.left ⟶ t.left)
(vm : s.middle ⟶ t.middle)
(vr : s.right ⟶ t.right)
(comm1 : s.lm ≫ vm = vl ≫ t.lm)
(comm2 : s.mr ≫ vr = vm ≫ t.mr)

instance pre_ses.categroy : category (pre_ses C) :=
{ hom := pre_ses.morphism C,
  id := λ s, 
  { vl := 𝟙 _,
    vm := 𝟙 _,
    vr := 𝟙 _,
  comm1 := by rw [category.comp_id, category.id_comp],
  comm2 := by rw [category.comp_id, category.id_comp] },
  comp := λ a b c m n, 
  { vl := m.vl ≫ n.vl,
    vm := m.vm ≫ n.vm,
    vr := m.vr ≫ n.vr,
  comm1 := by rw [← category.assoc, m.comm1, category.assoc _ n.vl, ←n.comm1, category.assoc],
  comm2 := by rw [← category.assoc, m.comm2, category.assoc _ n.vm, ←n.comm2, category.assoc] },
  id_comp' := by { intros, ext; { dsimp, rw category.id_comp, } },
  comp_id' := by { intros, ext; { dsimp, rw category.comp_id } },
  assoc' := by { intros, ext; { dsimp, rw category.assoc } } }

variables {C}

class pre_ses.is_exact (s : pre_ses C) : Prop :=
(exact1 : exact (0 : 0 ⟶ s.left) s.lm)
(exact2 : exact s.lm s.mr)
(exact3 : exact s.mr (0 : s.right ⟶ 0))

namespace pre_ses

variables {C D} 

@[simps]
def induced (s : pre_ses C) (F : C ⥤ D) : pre_ses D :=
{ left := F.obj s.left,
  middle := F.obj s.middle,
  right := F.obj s.right,
  lm := F.map s.lm,
  mr := F.map s.mr }

end pre_ses

variables {C D}

class functor.is_exact (F : C ⥤ D) : Prop :=
(map_exact : ∀ (s : pre_ses C), s.is_exact → (s.induced F).is_exact)

@[priority 100]
instance functor.preserves_finite_limits_of_is_exact (F : C ⥤ D) [F.is_exact] :
  preserves_finite_limits F :=
sorry

@[priority 100]
instance functor.preserves_finite_colimits_of_is_exact (F : C ⥤ D) [F.is_exact] :
  preserves_finite_colimits F :=
sorry

instance functor.is_exact_of_preserves_finite_limits_and_colimits (F : C ⥤ D)
  [preserves_finite_limits F] [preserves_finite_colimits F] : F.is_exact :=
sorry

variables (C)
@[derive [category]]
def ses := full_subcategory (λ (s : pre_ses C),  s.is_exact)

namespace ses

@[simps]
def induced (s : ses C) (F : C ⥤ D) [F.is_exact] : ses D :=
{ obj := s.obj.induced F,
  property := functor.is_exact.map_exact _ s.property }

end ses

end category_theory
