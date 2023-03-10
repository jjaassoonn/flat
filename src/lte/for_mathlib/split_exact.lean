/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang
-/
import category_theory.abelian.diagram_lemmas.four

/-!
# Short exact sequences, and splittings.

`short_exact f g` is the proposition that `0 ā¶ A -fā¶ B -gā¶ C ā¶ 0` is an exact sequence.

We define when a short exact sequence is left-split, right-split, and split.

In an abelian category, a left-split short exact sequence admits a splitting.
-/

noncomputable theory

open category_theory category_theory.limits category_theory.preadditive

variables {š : Type*} [category š]

namespace category_theory

variables {A B C A' B' C' : š} (f : A ā¶ B) (g : B ā¶ C) (f' : A' ā¶ B') (g' : B' ā¶ C')

section has_zero_morphisms

variables [has_zero_morphisms š] [has_kernels š] [has_images š]

/-- If `f : A ā¶ B` and `g : B ā¶ C` then `short_exact f g` is the proposition saying
  the resulting diagram `0 ā¶ A ā¶ B ā¶ C ā¶ 0` is an exact sequence. -/
structure short_exact : Prop :=
[mono  : mono f]
[epi   : epi g]
(exact : exact f g)

open_locale zero_object

-- TODO move
instance zero_to_zero_is_iso {C : Type*} [category C] [has_zero_object C] (f : (0 : C) ā¶ 0) :
  is_iso f :=
by convert (show is_iso (š (0 : C)), by apply_instance)


/-- An exact sequence `A -fā¶ B -gā¶ C` is *left split*
if there exists a morphism `Ļ : B ā¶ A` such that `f ā« Ļ = š A` and `g` is epi.

Such a sequence is automatically short exact (i.e., `f` is mono). -/
structure left_split : Prop :=
(left_split : ā Ļ : B ā¶ A, f ā« Ļ = š A)
[epi   : epi g]
(exact : exact f g)

lemma left_split.short_exact {f : A ā¶ B} {g : B ā¶ C} (h : left_split f g) : short_exact f g :=
{ mono :=
  begin
    obtain āØĻ, hĻā© := h.left_split,
    haveI : mono (f ā« Ļ) := by { rw hĻ, apply_instance },
    exact mono_of_mono f Ļ,
  end,
  epi := h.epi,
  exact := h.exact }

/-- An exact sequence `A -fā¶ B -gā¶ C` is *right split*
if there exists a morphism `Ļ : C ā¶ B` such that `f ā« Ļ = š A` and `f` is mono.

Such a sequence is automatically short exact (i.e., `g` is epi). -/
structure right_split : Prop :=
(right_split : ā Ļ : C ā¶ B, Ļ ā« g = š C)
[mono  : mono f]
(exact : exact f g)

lemma right_split.short_exact {f : A ā¶ B} {g : B ā¶ C} (h : right_split f g) : short_exact f g :=
{ epi :=
  begin
    obtain āØĻ, hĻā© := h.right_split,
    haveI : epi (Ļ ā« g) := by { rw hĻ, apply_instance },
    exact epi_of_epi Ļ g,
  end,
  mono := h.mono,
  exact := h.exact }

end has_zero_morphisms

section preadditive

variables [preadditive š]

/-- An exact sequence `A -fā¶ B -gā¶ C` is *split* if there exist
`Ļ : B ā¶ A` and `Ļ : C ā¶ B` such that:
* `f ā« Ļ = š A`
* `Ļ ā« g = š C`
* `f ā« g = 0`
* `Ļ ā« Ļ = 0`
* `Ļ ā« f + g ā« Ļ = š B`

Such a sequence is automatically short exact (i.e., `f` is mono and `g` is epi). -/
structure split : Prop :=
(split : ā (Ļ : B ā¶ A) (Ļ : C ā¶ B),
  f ā« Ļ = š A ā§ Ļ ā« g = š C ā§ f ā« g = 0 ā§ Ļ ā« Ļ = 0 ā§ Ļ ā« f + g ā« Ļ = š B)

variables [has_kernels š] [has_images š]

lemma exact_of_split {A B C : š} (f : A ā¶ B) (g : B ā¶ C) (Ļ : C ā¶ B) (Ļ : B ā¶ A)
  (hfg : f ā« g = 0) (H : Ļ ā« f + g ā« Ļ = š B) : exact f g :=
{ w := hfg,
  epi :=
  begin
    let Ļ : (kernel_subobject g : š) ā¶ image_subobject f :=
      subobject.arrow _ ā« Ļ ā« factor_thru_image_subobject f,
    suffices : Ļ ā« image_to_kernel f g hfg = š _,
    { convert epi_of_epi Ļ _, rw this, apply_instance },
    rw ā cancel_mono (subobject.arrow _), swap, { apply_instance },
    simp only [image_to_kernel_arrow, image_subobject_arrow_comp, category.id_comp, category.assoc],
    calc (kernel_subobject g).arrow ā« Ļ ā« f
        = (kernel_subobject g).arrow ā« š B : _
    ... = (kernel_subobject g).arrow        : category.comp_id _,
    rw [ā H, preadditive.comp_add],
    simp only [add_zero, zero_comp, kernel_subobject_arrow_comp_assoc],
  end }

section

variables {f g}

lemma split.exact (h : split f g) : exact f g :=
by { obtain āØĻ, Ļ, -, -, h1, -, h2ā© := h, exact exact_of_split f g Ļ Ļ h1 h2 }

lemma split.left_split (h : split f g) : left_split f g :=
{ left_split := by { obtain āØĻ, Ļ, h1, -ā© := h, exact āØĻ, h1ā©, },
  epi := begin
    obtain āØĻ, Ļ, -, h2, -ā© := h,
    have : epi (Ļ ā« g), { rw h2, apply_instance },
    exactI epi_of_epi Ļ g,
  end,
  exact := h.exact }

lemma split.right_split (h : split f g) : right_split f g :=
{ right_split := by { obtain āØĻ, Ļ, -, h1, -ā© := h, exact āØĻ, h1ā©, },
  mono := begin
    obtain āØĻ, Ļ, h1, -ā© := h,
    have : mono (f ā« Ļ), { rw h1, apply_instance },
    exactI mono_of_mono f Ļ,
  end,
  exact := h.exact }

lemma split.short_exact (h : split f g) : short_exact f g :=
h.left_split.short_exact

end

lemma split.map {š ā¬ : Type*} [category š] [abelian š] [category ā¬] [abelian ā¬] (F : š ā„¤ ā¬)
  [functor.additive F] {A B C : š} (f : A ā¶ B) (g : B ā¶ C) (h : split f g) :
  split (F.map f) (F.map g) :=
begin
  obtain āØĻ, Ļ, h1, h2, h3, h4, h5ā© := h,
  refine āØāØF.map Ļ, F.map Ļ, _ā©ā©,
  simp only [ā F.map_comp, ā F.map_id, ā F.map_add, F.map_zero, *, eq_self_iff_true, and_true],
end

/-- The sequence `A ā¶ A ā B ā¶ B` is exact. -/
lemma exact_inl_snd [has_binary_biproducts š] (A B : š) :
  exact (biprod.inl : A ā¶ A ā B) biprod.snd :=
exact_of_split _ _ biprod.inr biprod.fst biprod.inl_snd biprod.total

/-- The sequence `B ā¶ A ā B ā¶ A` is exact. -/
lemma exact_inr_fst [has_binary_biproducts š] (A B : š) :
  exact (biprod.inr : B ā¶ A ā B) biprod.fst :=
exact_of_split _ _ biprod.inl biprod.snd biprod.inr_fst ((add_comm _ _).trans biprod.total)

end preadditive

section abelian

variables [abelian š]
open_locale zero_object

lemma is_iso_of_short_exact_of_is_iso_of_is_iso (h : short_exact f g) (h' : short_exact f' g')
  (iā : A ā¶ A') (iā : B ā¶ B') (iā : C ā¶ C')
  (commā : iā ā« f' = f ā« iā) (commā : iā ā« g' = g ā« iā) [is_iso iā] [is_iso iā] :
  is_iso iā :=
begin
  obtain āØ_ā© := h,
  obtain āØ_ā© := h',
  resetI,
  refine @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso š _ _ 0 _ _ _ 0 _ _ _
    0 f g 0 f' g' 0 iā iā iā _ commā commā 0 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _;
  try { simp };
  try { apply exact_zero_left_of_mono };
  try { assumption };
  rwa ā epi_iff_exact_zero_right,
end

end abelian

/-- A *splitting* of a sequence `A -fā¶ B -gā¶ C` is an isomorphism
to the short exact sequence `0 ā¶ A ā¶ A ā C ā¶ C ā¶ 0` such that
the vertical maps on the left and the right are the identity. -/
@[nolint has_inhabited_instance]
structure splitting [has_zero_morphisms š] [has_binary_biproducts š] :=
(iso : B ā A ā C)
(comp_iso_eq_inl : f ā« iso.hom = biprod.inl)
(iso_comp_snd_eq : iso.hom ā« biprod.snd = g)

variables {f g}

namespace splitting

section has_zero_morphisms
variables [has_zero_morphisms š] [has_binary_biproducts š]

attribute [simp, reassoc] comp_iso_eq_inl iso_comp_snd_eq

variables (h : splitting f g)

@[simp, reassoc] lemma inl_comp_iso_eq : biprod.inl ā« h.iso.inv = f :=
by rw [iso.comp_inv_eq, h.comp_iso_eq_inl]

@[simp, reassoc] lemma iso_comp_eq_snd : h.iso.inv ā« g = biprod.snd :=
by rw [iso.inv_comp_eq, h.iso_comp_snd_eq]

/-- If `h` is a splitting of `A -fā¶ B -gā¶ C`,
then `h.section : C ā¶ B` is the morphism satisfying `h.section ā« g = š C`. -/
def _root_.category_theory.splitting.section : C ā¶ B := biprod.inr ā« h.iso.inv

/-- If `h` is a splitting of `A -fā¶ B -gā¶ C`,
then `h.retraction : B ā¶ A` is the morphism satisfying `f ā« h.retraction = š A`. -/
def retraction : B ā¶ A := h.iso.hom ā« biprod.fst

@[simp, reassoc] lemma section_Ļ : h.section ā« g = š C := by { delta splitting.section, simp }

@[simp, reassoc] lemma Ī¹_retraction : f ā« h.retraction = š A := by { delta retraction, simp }

@[simp, reassoc] lemma section_retraction : h.section ā« h.retraction = 0 :=
by { delta splitting.section retraction, simp }

/-- The retraction in a splitting is a split mono. -/
protected def split_mono : split_mono f := āØh.retraction, by simpā©

/-- The section in a splitting is a split epi. -/
protected def split_epi : split_epi g := āØh.section, by simpā©

@[simp, reassoc] lemma inr_iso_inv : biprod.inr ā« h.iso.inv = h.section := rfl

@[simp, reassoc] lemma iso_hom_fst : h.iso.hom ā« biprod.fst = h.retraction := rfl

-- move this, add `iso_zero_biprod`
/-- If `Y` is a zero object, `X ā X ā Y` for any `X`. -/
@[simps]
def iso_biprod_zero {C : Type*} [category C] [has_zero_morphisms C]
  [has_binary_biproducts C] {X Y : C} (hY : is_zero Y) : X ā X ā Y :=
{ hom := biprod.inl,
  inv := biprod.fst,
  inv_hom_id' := begin
    apply category_theory.limits.biprod.hom_ext;
    simp only [category.assoc, biprod.inl_fst, category.comp_id, category.id_comp,
      biprod.inl_snd, comp_zero],
    apply hY.eq_of_tgt
  end }
.

/-- A short exact sequence of the form `X -fā¶ Y -0ā¶ Z` where `f` is an iso and `Z` is zero
has a splitting. -/
def splitting_of_is_iso_zero {X Y Z : š} (f : X ā¶ Y) [is_iso f] (hZ : is_zero Z) :
  splitting f (0 : Y ā¶ Z) :=
āØ(as_iso f).symm āŖā« iso_biprod_zero hZ, by simp [hZ.eq_of_tgt _ 0], by simpā©

include h

protected lemma mono : mono f :=
begin
  apply mono_of_mono _ h.retraction,
  rw h.Ī¹_retraction,
  apply_instance
end

protected lemma epi : epi g :=
begin
  apply_with (epi_of_epi h.section) { instances := ff },
  rw h.section_Ļ,
  apply_instance
end

instance : mono h.section :=
by { delta splitting.section, apply_instance }

instance : epi h.retraction :=
by { delta retraction, apply epi_comp }

end has_zero_morphisms

section preadditive
variables [preadditive š] [has_binary_biproducts š]
variables (h : splitting f g)

lemma split_add : h.retraction ā« f + g ā« h.section = š _ :=
begin
  delta splitting.section retraction,
  rw [ā cancel_mono h.iso.hom, ā cancel_epi h.iso.inv],
  simp only [category.comp_id, category.id_comp, category.assoc,
    iso.inv_hom_id_assoc, iso.inv_hom_id, limits.biprod.total,
    preadditive.comp_add, preadditive.add_comp,
    splitting.comp_iso_eq_inl, splitting.iso_comp_eq_snd_assoc]
end

@[reassoc]
lemma retraction_Ī¹_eq_id_sub :
  h.retraction ā« f = š _ - g ā« h.section :=
eq_sub_iff_add_eq.mpr h.split_add

@[reassoc]
lemma Ļ_section_eq_id_sub :
  g ā« h.section = š _ - h.retraction ā« f :=
eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h.split_add)

lemma splittings_comm (h h' : splitting f g) :
  h'.section ā« h.retraction = - h.section ā« h'.retraction :=
begin
  haveI := h.mono,
  rw ā cancel_mono f,
  simp [retraction_Ī¹_eq_id_sub],
end

include h

lemma split : split f g :=
begin
  let Ļ := h.iso.hom ā« biprod.fst,
  let Ļ := biprod.inr ā« h.iso.inv,
  refine āØāØh.retraction, h.section, h.Ī¹_retraction, h.section_Ļ, _,
    h.section_retraction, h.split_addā©ā©,
  rw [ā h.inl_comp_iso_eq, category.assoc, h.iso_comp_eq_snd, biprod.inl_snd],
end

@[reassoc] lemma comp_eq_zero : f ā« g = 0 :=
h.split.1.some_spec.some_spec.2.2.1

variables [has_kernels š] [has_images š] [has_zero_object š] [has_cokernels š]

protected lemma exact : exact f g :=
begin
  rw exact_iff_exact_of_iso f g (biprod.inl : A ā¶ A ā C) (biprod.snd : A ā C ā¶ C) _ _ _,
  { exact exact_inl_snd _ _ },
  { refine arrow.iso_mk (iso.refl _) h.iso _,
    simp only [iso.refl_hom, arrow.mk_hom, category.id_comp, comp_iso_eq_inl], },
  { refine arrow.iso_mk h.iso (iso.refl _) _,
    simp only [iso.refl_hom, arrow.mk_hom, category.comp_id, iso_comp_snd_eq],
    erw category.comp_id /- why ?? -/ },
  { refl }
end

protected
lemma short_exact : short_exact f g :=
{ mono := h.mono, epi := h.epi, exact := h.exact }

end preadditive

section abelian
variables [abelian š]

-- TODO: this should be generalized to isoms of short sequences,
-- because now it forces one direction, and we want both.
/-- To construct a splitting of `A -fā¶ B -gā¶ C` it suffices to supply
a *morphism* `i : B ā¶ A ā C` such that `f ā« i` is the canonical map `biprod.inl : A ā¶ A ā C` and
`i ā« q = g`, where `q` is the canonical map `biprod.snd : A ā C ā¶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is than automatically an isomorphism. -/
def mk' (h : short_exact f g) (i : B ā¶ A ā C) (h1 : f ā« i = biprod.inl) (h2 : i ā« biprod.snd = g) :
  splitting f g :=
{ iso :=
  begin
    refine @as_iso _ _ _ _ i (id _),
    refine is_iso_of_short_exact_of_is_iso_of_is_iso f g _ _ h _ _ _ _
      (h1.trans (category.id_comp _).symm).symm (h2.trans (category.comp_id _).symm),
    split,
    apply exact_inl_snd
  end,
  comp_iso_eq_inl := by { rwa as_iso_hom, },
  iso_comp_snd_eq := h2 }

end abelian

end splitting

section
variables [abelian š]

/-- A short exact sequence that is left split admits a splitting. -/
def left_split.splitting {f : A ā¶ B} {g : B ā¶ C} (h : left_split f g) : splitting f g :=
splitting.mk' h.short_exact (biprod.lift h.left_split.some g)
(by { ext,
  { simpa only [biprod.inl_fst, biprod.lift_fst, category.assoc] using h.left_split.some_spec },
  { simp only [biprod.inl_snd, biprod.lift_snd, category.assoc, h.exact.w], } })
(by { simp only [biprod.lift_snd], })

end

end category_theory