import .snake_lemma
import .exact_seq2

noncomputable theory

open category_theory category_theory.limits

variables {ð : Type*} [category ð] [abelian ð]
variables (Aâ Bâ Câ : ð)
variables (Aâ Bâ Câ : ð)
variables (Aâ Bâ Câ : ð)
variables (Aâ Bâ Câ : ð)
variables (fâ : Aâ â¶ Bâ) (gâ : Bâ â¶ Câ)
variables (aâ : Aâ â¶ Aâ) (bâ : Bâ â¶ Bâ) (câ : Câ â¶ Câ)
variables (fâ : Aâ â¶ Bâ) (gâ : Bâ â¶ Câ)
variables (aâ : Aâ â¶ Aâ) (bâ : Bâ â¶ Bâ) (câ : Câ â¶ Câ)
variables (fâ : Aâ â¶ Bâ) (gâ : Bâ â¶ Câ)
variables (aâ : Aâ â¶ Aâ) (bâ : Bâ â¶ Bâ) (câ : Câ â¶ Câ)
variables (fâ : Aâ â¶ Bâ) (gâ : Bâ â¶ Câ)

namespace category_theory

local notation `kernel_map`   := kernel.map _ _ _ _
local notation `cokernel_map` := cokernel.map _ _ _ _

structure snake : Prop :=
(row_exactâ : exact fâ gâ)
(row_exactâ : exact fâ gâ)
[row_epi : epi gâ]
[row_mono : mono fâ]
(col_exact_a : exact_seq ð [aâ, aâ, aâ])
(col_exact_b : exact_seq ð [bâ, bâ, bâ])
(col_exact_c : exact_seq ð [câ, câ, câ])
[col_mono_a : mono aâ]
[col_mono_b : mono bâ]
[col_mono_c : mono câ]
[col_epi_a : epi aâ]
[col_epi_b : epi bâ]
[col_epi_c : epi câ]
(sq_aâ : aâ â« fâ = fâ â« bâ)
(sq_bâ : bâ â« gâ = gâ â« câ)
(sq_aâ : aâ â« fâ = fâ â« bâ)
(sq_bâ : bâ â« gâ = gâ â« câ)
(sq_aâ : aâ â« fâ = fâ â« bâ)
(sq_bâ : bâ â« gâ = gâ â« câ)

namespace snake

lemma mk_of_sequence_hom (sqâ : aâ â« fâ = fâ â« bâ) (sqâ : bâ â« gâ = gâ â« câ)
  (hâ : exact fâ gâ) (hâ : exact fâ gâ) [epi gâ] [mono fâ] : snake
  (kernel aâ) (kernel bâ) (kernel câ)
  Aâ Bâ Câ
  Aâ Bâ Câ
  (cokernel aâ) (cokernel bâ) (cokernel câ)
  (kernel_map sqâ) (kernel_map sqâ)
  (kernel.Î¹ _) (kernel.Î¹ _) (kernel.Î¹ _)
  fâ gâ
  aâ bâ câ
  fâ gâ
  (cokernel.Ï _) (cokernel.Ï _) (cokernel.Ï _)
  (cokernel_map sqâ) (cokernel_map sqâ) :=
{ row_exactâ := hâ,
  row_exactâ := hâ,
  col_exact_a := exact_seq.cons _ _ exact_kernel_Î¹ _ $ (exact_iff_exact_seq _ _).mp (abelian.exact_cokernel _),
  col_exact_b := exact_seq.cons _ _ exact_kernel_Î¹ _ $ (exact_iff_exact_seq _ _).mp (abelian.exact_cokernel _),
  col_exact_c := exact_seq.cons _ _ exact_kernel_Î¹ _ $ (exact_iff_exact_seq _ _).mp (abelian.exact_cokernel _),
  sq_aâ := (limits.kernel.lift_Î¹ _ _ _).symm,
  sq_bâ := (limits.kernel.lift_Î¹ _ _ _).symm,
  sq_aâ := sqâ,
  sq_bâ := sqâ,
  sq_aâ := cokernel.Ï_desc _ _ _,
  sq_bâ := cokernel.Ï_desc _ _ _ }

variables
 {Aâ Bâ Câ
  Aâ Bâ Câ
  Aâ Bâ Câ
  Aâ Bâ Câ
  fâ gâ aâ bâ câ fâ gâ aâ bâ câ fâ gâ aâ bâ câ fâ gâ}

variables (S : snake
  Aâ Bâ Câ
  Aâ Bâ Câ
  Aâ Bâ Câ
  Aâ Bâ Câ
  fâ gâ aâ bâ câ fâ gâ aâ bâ câ fâ gâ aâ bâ câ fâ gâ)

variables

def snake_diagram : snake_diagram â¥¤ ð :=
snake_diagram.mk_functor
![![Aâ, Bâ, Câ],
  ![Aâ, Bâ, Câ],
  ![Aâ, Bâ, Câ],
  ![Aâ, Bâ, Câ]]
fâ gâ aâ bâ câ fâ gâ aâ bâ câ fâ gâ aâ bâ câ fâ gâ
S.sq_aâ S.sq_bâ S.sq_aâ S.sq_bâ S.sq_aâ S.sq_bâ

lemma is_snake_input : is_snake_input S.snake_diagram :=
{ row_exactâ := by { dsimp only [snake_diagram], simpa using S.row_exactâ, },
  row_exactâ := by { dsimp only [snake_diagram], simpa using S.row_exactâ },
  col_exactâ := begin
    intros j,
    dsimp only [snake_diagram],
    fin_cases j with [0, 1, 2]; simp; rw exact_iff_exact_seq,
    exacts [S.col_exact_a.extract 0 2, S.col_exact_b.extract 0 2, S.col_exact_c.extract 0 2],
  end,
  col_exactâ := begin
    intros j,
    dsimp only [snake_diagram],
    fin_cases j with [0, 1, 2]; simp; rw exact_iff_exact_seq,
    exacts [S.col_exact_a.extract 1 2, S.col_exact_b.extract 1 2, S.col_exact_c.extract 1 2],
  end,
  col_mono := begin
    intros j,
    dsimp only [snake_diagram],
    fin_cases j with [0, 1, 2]; simp,
    exacts [S.col_mono_a, S.col_mono_b, S.col_mono_c],
  end,
  col_epi := begin
    intros j,
    dsimp only [snake_diagram],
    fin_cases j with [0, 1, 2]; simp,
    exacts [S.col_epi_a, S.col_epi_b, S.col_epi_c],
  end,
  row_mono := by { dsimp only [snake_diagram], simp, exact S.row_mono },
  row_epi := by { dsimp only [snake_diagram], simpa using S.row_epi } }

def snake_input : snake_input ð := â¨S.snake_diagram, S.is_snake_inputâ©

def Î´ : Câ â¶ Aâ := S.is_snake_input.Î´

lemma six_term_exact_seq : exact_seq ð [fâ, gâ, S.Î´, fâ, gâ] :=
begin
  have := S.is_snake_input.six_term_exact_seq,
  dsimp only [snake_diagram] at this,
  simpa only [snake_diagram.mk_functor_map_f0, snake_diagram.mk_functor_map_g0,
    snake_diagram.mk_functor_map_f3, snake_diagram.mk_functor_map_g3],
end

end snake

lemma mono_of_exact_of_eq_zero (hfg : exact fâ gâ) (h : fâ = 0) : mono gâ :=
by rwa [(abelian.tfae_mono Aâ gâ).out 0 2, â h]

lemma cokernel.map_mono_of_epi_of_mono (sq : fâ â« bâ = aâ â« fâ)
  [epi aâ] [mono bâ] [mono fâ] :
  mono (cokernel.map fâ fâ aâ bâ sq) :=
begin
  have S := snake.mk_of_sequence_hom Aâ Bâ (cokernel fâ) Aâ Bâ (cokernel fâ)
    fâ (cokernel.Ï _) aâ bâ (cokernel.map fâ fâ aâ bâ sq) fâ (cokernel.Ï _) sq.symm (by simp)
    (abelian.exact_cokernel _) (abelian.exact_cokernel _),
  apply (S.col_exact_c).pair.mono_of_is_zero,
  exact (S.six_term_exact_seq.drop 1).pair.is_zero_of_is_zero_is_zero
    (is_zero_kernel_of_mono _) (is_zero_cokernel_of_epi _),
end

end category_theory