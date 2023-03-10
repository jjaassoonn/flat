import category_theory.preadditive.basic
import category_theory.abelian.projective
import category_theory.abelian.diagram_lemmas.four

import data.matrix.notation

import .abelian_category
import .fin_functor
import .split_exact

noncomputable theory

open category_theory
open category_theory.limits
open category_theory.preadditive

universes v u

namespace category_theory
variables (ð : Type u) [category.{v} ð]

@[ext]
structure short_exact_sequence [has_images ð] [has_zero_morphisms ð] [has_kernels ð] :=
(fst snd trd : ð)
(f : fst â¶ snd)
(g : snd â¶ trd)
[mono'  : mono f]
[epi'   : epi g]
(exact' : exact f g)

namespace short_exact_sequence

attribute [instance] mono' epi'

variables {ð} [has_images ð] [has_zero_morphisms ð] [has_kernels ð]

@[simp, reassoc] lemma f_comp_g (A : short_exact_sequence ð) : A.f â« A.g = 0 := A.exact'.w

@[ext]
structure hom (A B : short_exact_sequence ð) :=
(fst : A.1 â¶ B.1)
(snd : A.2 â¶ B.2)
(trd : A.3 â¶ B.3)
(sq1' : fst â« B.f = A.f â« snd . obviously)
(sq2' : snd â« B.g = A.g â« trd . obviously)

namespace hom

restate_axiom sq1' sq1
restate_axiom sq2' sq2

attribute [reassoc] sq1 sq2

end hom

instance : quiver (short_exact_sequence ð) := â¨homâ©

def id (A : short_exact_sequence ð) : A â¶ A :=
{ fst := ð _,
  snd := ð _,
  trd := ð _,
  sq1' := by simp only [category.id_comp, category.comp_id],
  sq2' := by simp only [category.id_comp, category.comp_id], }

def comp {A B C : short_exact_sequence ð} (f : A â¶ B) (g : B â¶ C) : A â¶ C :=
{ fst := f.1 â« g.1,
  snd := f.2 â« g.2,
  trd := f.3 â« g.3,
  sq1' := by rw [category.assoc, hom.sq1, hom.sq1_assoc],
  sq2' := by rw [category.assoc, hom.sq2, hom.sq2_assoc], }

instance : category (short_exact_sequence ð) :=
{ id := id,
  comp := Î» A B C f g, comp f g,
  id_comp' := by { intros, ext; dsimp; apply category.id_comp, },
  comp_id' := by { intros, ext; dsimp; apply category.comp_id, },
  assoc' := by { intros, ext; dsimp; apply category.assoc, },
  .. (infer_instance : quiver (short_exact_sequence ð)) }

@[simp] lemma id_fst (A : short_exact_sequence ð) : hom.fst (ð A) = ð A.1 := rfl
@[simp] lemma id_snd (A : short_exact_sequence ð) : hom.snd (ð A) = ð A.2 := rfl
@[simp] lemma id_trd (A : short_exact_sequence ð) : hom.trd (ð A) = ð A.3 := rfl

variables {A B C : short_exact_sequence ð} (f : A â¶ B) (g : B â¶ C)

@[simp, reassoc] lemma comp_fst : (f â« g).1 = f.1 â« g.1 := rfl
@[simp, reassoc] lemma comp_snd : (f â« g).2 = f.2 â« g.2 := rfl
@[simp, reassoc] lemma comp_trd : (f â« g).3 = f.3 â« g.3 := rfl

variables (ð)

@[simps] def Fst : short_exact_sequence ð â¥¤ ð :=
{ obj := fst, map := Î» A B f, f.1 }

@[simps] def Snd : short_exact_sequence ð â¥¤ ð :=
{ obj := snd, map := Î» A B f, f.2 }

@[simps] def Trd : short_exact_sequence ð â¥¤ ð :=
{ obj := trd, map := Î» A B f, f.3 }

@[simps] def f_nat : Fst ð â¶ Snd ð :=
{ app := Î» A, A.f,
  naturality' := Î» A B f, f.sq1 }

@[simps] def g_nat : Snd ð â¶ Trd ð :=
{ app := Î» A, A.g,
  naturality' := Î» A B f, f.sq2 }

instance : has_zero_morphisms (short_exact_sequence ð) :=
{ has_zero := Î» A B, â¨{ fst := 0, snd := 0, trd := 0 }â©,
  comp_zero' := by { intros, ext; apply comp_zero },
  zero_comp' := by { intros, ext; apply zero_comp }, }
.

@[simp] lemma hom_zero_fst : (0 : A â¶ B).1 = 0 := rfl

@[simp] lemma hom_zero_snd : (0 : A â¶ B).2 = 0 := rfl

@[simp] lemma hom_zero_trd : (0 : A â¶ B).3 = 0 := rfl

variables {ð}

protected def functor (A : short_exact_sequence ð) : fin 3 â¥¤ ð :=
fin3_functor_mk ![A.1, A.2, A.3] A.f A.g

def functor_map {A B : short_exact_sequence ð} (f : A â¶ B) :
  Î  i, A.functor.obj i â¶ B.functor.obj i
| â¨0,hâ© := f.1
| â¨1,hâ© := f.2
| â¨2,hâ© := f.3
| â¨i+3,hiâ© := by { exfalso, revert hi, dec_trivial }

meta def aux_tac : tactic unit :=
`[simp only [hom_of_le_refl, functor.map_id, category.id_comp, category.comp_id]]

lemma functor_map_naturality {A B : short_exact_sequence ð} (f : A â¶ B) :
  â (i j : fin 3) (hij : i â¤ j),
    functor_map f i â« B.functor.map hij.hom = A.functor.map hij.hom â« functor_map f j
| â¨0,hiâ© â¨0,hjâ© hij := by aux_tac
| â¨1,hiâ© â¨1,hjâ© hij := by aux_tac
| â¨2,hiâ© â¨2,hjâ© hij := by aux_tac
| â¨0,hiâ© â¨1,hjâ© hij := f.sq1
| â¨1,hiâ© â¨2,hjâ© hij := f.sq2
| â¨i+3,hiâ© _ _ := by { exfalso, revert hi, dec_trivial }
| _ â¨j+3,hjâ© _ := by { exfalso, revert hj, dec_trivial }
| â¨i+1,hiâ© â¨0,hjâ© H := by { exfalso, revert H, dec_trivial }
| â¨i+2,hiâ© â¨1,hjâ© H := by { exfalso, revert H, dec_trivial }
| â¨0,hiâ© â¨2,hjâ© hij :=
begin
  have h01 : (0 : fin 3) â¶ 1 := hom_of_le dec_trivial,
  have h12 : (1 : fin 3) â¶ 2 := hom_of_le dec_trivial,
  calc functor_map f â¨0, hiâ© â« B.functor.map hij.hom
      = functor_map f â¨0, hiâ© â« B.functor.map h01 â« B.functor.map h12 : _
  ... = (functor_map f â¨0, hiâ© â« B.functor.map h01) â« B.functor.map h12 : by rw category.assoc
  ... = (A.functor.map h01 â« functor_map f _) â« B.functor.map h12 : _
  ... = A.functor.map h01 â« functor_map f _ â« B.functor.map h12 : category.assoc _ _ _
  ... = A.functor.map h01 â« A.functor.map h12 â« functor_map f _ : _
  ... = A.functor.map hij.hom â« functor_map f â¨2, hjâ© : _,
  { rw [â functor.map_comp], congr, },
  { congr' 1, exact f.sq1 },
  { congr' 1, exact f.sq2 },
  { rw [â functor.map_comp_assoc], congr, },
end

@[simps] def Functor : short_exact_sequence ð â¥¤ fin 3 â¥¤ ð :=
{ obj := short_exact_sequence.functor,
  map := Î» A B f,
  { app := functor_map f,
    naturality' := Î» i j hij, (functor_map_naturality f i j hij.le).symm },
  map_id' := Î» A, by { ext i, fin_cases i; refl },
  map_comp' := Î» A B C f g, by { ext i, fin_cases i; refl } }

end short_exact_sequence

namespace short_exact_sequence

variables {ð} [abelian ð]
variables {A B C : short_exact_sequence ð} (f : A â¶ B) (g : B â¶ C)

section iso

variables {A B C} (f g)

open_locale zero_object

/-- One form of the five lemma: if a morphism of short exact sequences has isomorphisms
as first and third component, then the second component is also an isomorphism. -/
lemma snd_is_iso (h1 : is_iso f.1) (h3 : is_iso f.3) : is_iso f.2 :=
@abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso ð _ _
  0 A.1 A.2 A.3
  0 B.1 B.2 B.3
  0 A.f A.g
  0 B.f B.g
  0 f.1 f.2 f.3 (by rw [zero_comp, zero_comp]) f.sq1 f.sq2
  0 0
  0 0 0 (by rw [comp_zero, comp_zero])
  (exact_zero_left_of_mono _)
  A.exact'
  ((epi_iff_exact_zero_right _).mp infer_instance)
  (exact_zero_left_of_mono _)
  B.exact'
  ((epi_iff_exact_zero_right _).mp infer_instance) _ _ _ _

/-- One form of the five lemma: if a morphism `f` of short exact sequences has isomorphisms
as first and third component, then `f` itself is an isomorphism. -/
lemma is_iso_of_fst_of_trd (h1 : is_iso f.1) (h3 : is_iso f.3) : is_iso f :=
{ out :=
  begin
    haveI : is_iso f.2 := snd_is_iso f h1 h3,
    refine â¨â¨inv f.1, inv f.2, inv f.3, _, _â©, _, _â©,
    { dsimp, simp only [is_iso.inv_comp_eq, f.sq1_assoc, category.comp_id, is_iso.hom_inv_id], },
    { dsimp, simp only [is_iso.inv_comp_eq, f.sq2_assoc, category.comp_id, is_iso.hom_inv_id], },
    { ext; dsimp; simp only [is_iso.hom_inv_id], },
    { ext; dsimp; simp only [is_iso.inv_hom_id], },
  end }

@[simps] def iso_of_components (fâ : A.1 â B.1) (fâ : A.2 â B.2) (fâ : A.3 â B.3)
  (sq1 : fâ.hom â« B.f = A.f â« fâ.hom) (sq2 : fâ.hom â« B.g = A.g â« fâ.hom) :
  A â B :=
{ hom := â¨fâ.hom, fâ.hom, fâ.hom, sq1, sq2â©,
  inv :=
  begin
    refine â¨fâ.inv, fâ.inv, fâ.inv, _, _â©; dsimp,
    rw [iso.inv_comp_eq, â category.assoc, iso.eq_comp_inv, sq1],
    rw [iso.inv_comp_eq, â category.assoc, iso.eq_comp_inv, sq2],
  end,
  hom_inv_id' := by { ext; apply iso.hom_inv_id, },
  inv_hom_id' := by { ext; apply iso.inv_hom_id, } }

@[simps] def iso_of_components' (fâ : A.1 â B.1) (fâ : A.2 â¶ B.2) (fâ : A.3 â B.3)
  (sq1 : fâ.hom â« B.f = A.f â« fâ) (sq2 : fâ â« B.g = A.g â« fâ.hom) :
  A â B :=
let F : A â¶ B := â¨fâ.hom, fâ, fâ.hom, sq1, sq2â© in
{ hom := F,
  inv :=
  begin
    haveI : is_iso F.2 := snd_is_iso _ infer_instance infer_instance,
    refine â¨fâ.inv, inv F.2, fâ.inv, _, _â©; dsimp,
    rw [iso.inv_comp_eq, â category.assoc, is_iso.eq_comp_inv, sq1],
    rw [is_iso.inv_comp_eq, â category.assoc, iso.eq_comp_inv, sq2],
  end,
  hom_inv_id' := by { ext; try { apply iso.hom_inv_id, }, apply is_iso.hom_inv_id },
  inv_hom_id' := by { ext; try { apply iso.inv_hom_id, }, apply is_iso.inv_hom_id } }

end iso

section split

/-- A short exact sequence `0 â¶ Aâ -fâ¶ Aâ -gâ¶ Aâ â¶ 0` is *left split*
if there exists a morphism `Ï : Aâ â¶ Aâ` such that `f â« Ï = ð Aâ`. -/
def left_split (A : short_exact_sequence ð) : Prop :=
â Ï : A.2 â¶ A.1, A.f â« Ï = ð A.1

/-- A short exact sequence `0 â¶ Aâ -fâ¶ Aâ -gâ¶ Aâ â¶ 0` is *right split*
if there exists a morphism `Ï : Aâ â¶ Aâ` such that `f â« Ï = ð Aâ`. -/
def right_split (A : short_exact_sequence ð) : Prop :=
â Ï : A.3 â¶ A.2, Ï â« A.g = ð A.3

variables {ð : Type*} [category ð] [abelian ð]

lemma exact_of_split {A B C : ð} (f : A â¶ B) (g : B â¶ C) (Ï : C â¶ B) (Ï : B â¶ A)
  (hfg : f â« g = 0) (H : Ï â« f + g â« Ï = ð B) : exact f g :=
{ w := hfg,
  epi :=
  begin
    let Ï : (kernel_subobject g : ð) â¶ image_subobject f :=
      subobject.arrow _ â« Ï â« factor_thru_image_subobject f,
    suffices : Ï â« image_to_kernel f g hfg = ð _,
    { convert epi_of_epi Ï _, rw this, apply_instance },
    rw â cancel_mono (subobject.arrow _), swap, { apply_instance },
    simp only [image_to_kernel_arrow, image_subobject_arrow_comp, category.id_comp, category.assoc],
    calc (kernel_subobject g).arrow â« Ï â« f
        = (kernel_subobject g).arrow â« ð B : _
    ... = (kernel_subobject g).arrow        : category.comp_id _,
    rw [â H, preadditive.comp_add],
    simp only [add_zero, zero_comp, kernel_subobject_arrow_comp_assoc],
  end }

-- move this
lemma exact_inl_snd (A B : ð) : exact (biprod.inl : A â¶ A â B) biprod.snd :=
exact_of_split _ _ biprod.inr biprod.fst biprod.inl_snd biprod.total

def mk_of_split {A B C : ð} (f : A â¶ B) (g : B â¶ C) (Ï : B â¶ A) (Ï : C â¶ B)
  (hfg : f â« g = 0) (hÏ : f â« Ï = ð A) (hÏ : Ï â« g = ð C) (H : Ï â« f + g â« Ï = ð B) :
  short_exact_sequence ð :=
{ fst := A,
  snd := B,
  trd := C,
  f := f,
  g := g,
  mono' := by { haveI : mono (f â« Ï), { rw hÏ, apply_instance }, exact mono_of_mono f Ï, },
  epi' := by { haveI : epi (Ï â« g), { rw hÏ, apply_instance }, exact epi_of_epi Ï g, },
  exact' := exact_of_split f g Ï Ï hfg H }

def mk_of_split' {A B C : ð} (f : A â¶ B) (g : B â¶ C)
  (H : â (Ï : B â¶ A) (Ï : C â¶ B), f â« g = 0 â§ f â« Ï = ð A â§ Ï â« g = ð C â§ Ï â« f + g â« Ï = ð B) :
  short_exact_sequence ð :=
mk_of_split f g H.some H.some_spec.some H.some_spec.some_spec.1 H.some_spec.some_spec.2.1
  H.some_spec.some_spec.2.2.1 H.some_spec.some_spec.2.2.2

@[simp] def mk_split (A B : ð) : short_exact_sequence ð :=
{ fst := A,
  snd := A â B,
  trd := B,
  f := biprod.inl,
  g := biprod.snd,
  exact' := exact_inl_snd _ _ }

/-- A *splitting* of a short exact sequence `0 â¶ Aâ -fâ¶ Aâ -gâ¶ Aâ â¶ 0` is
an isomorphism to the short exact sequence `0 â¶ Aâ â¶ Aâ â Aâ â¶ Aâ â¶ 0`,
where the left and right components of the isomorphism are identity maps. -/
structure splitting (A : short_exact_sequence ð) extends A â (mk_split A.1 A.3) :=
(fst_eq_id : hom.1 = ð A.1)
(trd_eq_id : hom.3 = ð A.3)

/-- A short exact sequence `0 â¶ Aâ -fâ¶ Aâ -gâ¶ Aâ â¶ 0` is *split* if there exist
`Ï : Aâ â¶ Aâ` and `Ï : Aâ â¶ Aâ` such that:
* `f â« Ï = ð Aâ`
* `Ï â« g = ð Aâ`
* `Ï â« Ï = 0`
* `Ï â« f + g â« Ï = ð Aâ`
-/
def split (A : short_exact_sequence ð) : Prop :=
â (Ï : A.2 â¶ A.1) (Ï : A.3 â¶ A.2),
   A.f â« Ï = ð A.1 â§ Ï â« A.g = ð A.3 â§ Ï â« Ï = 0 â§ Ï â« A.f + A.g â« Ï = ð A.2

lemma mk_split_split (A B : ð) : (mk_split A B).split :=
â¨biprod.fst, biprod.inr, biprod.inl_fst, biprod.inr_snd, biprod.inr_fst, biprod.totalâ©

lemma splitting.split {A : short_exact_sequence ð} (i : splitting A) : A.split :=
begin
  refine â¨i.hom.2 â« biprod.fst â« i.inv.1, i.hom.3 â« biprod.inr â« i.inv.2, _â©,
  simp only [category.assoc, â hom.sq1_assoc, hom.sq2], dsimp,
  simp only [biprod.inl_fst_assoc, biprod.inr_snd_assoc, category.comp_id, category.assoc,
    â comp_fst, â comp_snd_assoc, â comp_trd, i.to_iso.hom_inv_id, i.to_iso.inv_hom_id],
  dsimp,
  simp only [true_and, biprod.inr_fst_assoc, zero_comp, eq_self_iff_true, comp_zero,
    category.id_comp],
  simp only [hom.sq1, â hom.sq2_assoc, â comp_add],
  simp only [â category.assoc, â add_comp, biprod.total,
    category.comp_id, â comp_snd, i.to_iso.hom_inv_id], refl,
end

def left_split.splitting {A : short_exact_sequence ð} (h : A.left_split) : A.splitting :=
{ to_iso := iso_of_components' (iso.refl _) (biprod.lift h.some A.g) (iso.refl _)
    (by { dsimp, simp only [category.id_comp], ext,
      { simpa only [biprod.inl_fst, biprod.lift_fst, category.assoc] using h.some_spec.symm, },
      { simp only [exact.w, f_comp_g, biprod.lift_snd, category.assoc, exact_inl_snd] } })
    (by { dsimp, simp only [category.comp_id, biprod.lift_snd], }),
  fst_eq_id := rfl,
  trd_eq_id := rfl }

def right_split.splitting {A : short_exact_sequence ð} (h : A.right_split) : A.splitting :=
{ to_iso := iso.symm $ iso_of_components' (iso.refl _) (biprod.desc A.f h.some) (iso.refl _)
    (by { dsimp, simp only [biprod.inl_desc, category.id_comp], })
    (by { dsimp, simp only [category.comp_id], ext,
      { simp only [exact.w, f_comp_g, biprod.inl_desc_assoc, exact_inl_snd] },
      { simpa only [biprod.inr_snd, biprod.inr_desc_assoc] using h.some_spec, } }),
  fst_eq_id := rfl,
  trd_eq_id := rfl }

lemma tfae_split (A : short_exact_sequence ð) :
  tfae [A.left_split, A.right_split, A.split, nonempty A.splitting] :=
begin
  tfae_have : 3 â 1, { rintro â¨Ï, Ï, hÏ, hÏ, hÏÏ, Hâ©, exact â¨Ï, hÏâ© },
  tfae_have : 3 â 2, { rintro â¨Ï, Ï, hÏ, hÏ, hÏÏ, Hâ©, exact â¨Ï, hÏâ© },
  tfae_have : 4 â 3, { rintro â¨iâ©, exact i.split, },
  tfae_have : 1 â 4, { intro h, exact â¨h.splittingâ© },
  tfae_have : 2 â 4, { intro h, exact â¨h.splittingâ© },
  tfae_finish
end

end split

end short_exact_sequence

namespace short_exact_sequence

open category_theory.preadditive

variables {ð} [preadditive ð] [has_images ð] [has_kernels ð]
variables (A B : short_exact_sequence ð)

local notation `Ïâ` := congr_arg _root_.prod.fst
local notation `Ïâ` := congr_arg _root_.prod.snd

protected def hom_inj (f : A â¶ B) : (A.1 â¶ B.1) Ã (A.2 â¶ B.2) Ã (A.3 â¶ B.3) := â¨f.1, f.2, f.3â©

protected lemma hom_inj_injective : function.injective (short_exact_sequence.hom_inj A B) :=
Î» f g h, let aux := Ïâ h in
by { ext; [have := Ïâ h, have := Ïâ aux, have := Ïâ aux]; exact this, }

instance : has_add (A â¶ B) :=
{ add := Î» f g,
  { fst := f.1 + g.1,
    snd := f.2 + g.2,
    trd := f.3 + g.3,
    sq1' := by { rw [add_comp, comp_add, f.sq1, g.sq1], },
    sq2' := by { rw [add_comp, comp_add, f.sq2, g.sq2], } } }

instance : has_neg (A â¶ B) :=
{ neg := Î» f,
  { fst := -f.1,
    snd := -f.2,
    trd := -f.3,
    sq1' := by { rw [neg_comp, comp_neg, f.sq1], },
    sq2' := by { rw [neg_comp, comp_neg, f.sq2], } } }

instance : has_sub (A â¶ B) :=
{ sub := Î» f g,
  { fst := f.1 - g.1,
    snd := f.2 - g.2,
    trd := f.3 - g.3,
    sq1' := by { rw [sub_comp, comp_sub, f.sq1, g.sq1], },
    sq2' := by { rw [sub_comp, comp_sub, f.sq2, g.sq2], } } }

instance has_nsmul : has_smul â (A â¶ B) :=
{ smul := Î» n f,
  { fst := n â¢ f.1,
    snd := n â¢ f.2,
    trd := n â¢ f.3,
    sq1' := by rw [nsmul_comp, comp_nsmul, f.sq1],
    sq2' := by rw [nsmul_comp, comp_nsmul, f.sq2] } }

instance has_zsmul : has_smul â¤ (A â¶ B) :=
{ smul := Î» n f,
  { fst := n â¢ f.1,
    snd := n â¢ f.2,
    trd := n â¢ f.3,
    sq1' := by rw [zsmul_comp, comp_zsmul, f.sq1],
    sq2' := by rw [zsmul_comp, comp_zsmul, f.sq2] } }

variables (ð)

instance : preadditive (short_exact_sequence ð) :=
{ hom_group := Î» A B, (short_exact_sequence.hom_inj_injective A B).add_comm_group _
  rfl (Î» _ _, rfl) (Î» _, rfl) (Î» _ _, rfl) (Î» _ _, rfl) (Î» _ _, rfl),
  add_comp' := by { intros, ext; apply add_comp },
  comp_add' := by { intros, ext; apply comp_add }, }
.

instance Fst_additive : (Fst ð).additive := {}
instance Snd_additive : (Snd ð).additive := {}
instance Trd_additive : (Trd ð).additive := {}

end short_exact_sequence

end category_theory