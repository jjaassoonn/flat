import data.real.basic
import data.real.sqrt

def S : set ℝ := { r | 0 ≤ r }

def abs' : ℝ → S :=
λ r, ⟨|r|, show 0 ≤ |r|, from abs_nonneg _⟩

def emb : S → ℝ :=
λ r, r.val

noncomputable def sqrt' : S → S :=
λ s, ⟨real.sqrt (s : ℝ), real.sqrt_nonneg _⟩