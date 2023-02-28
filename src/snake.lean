import linear_algebra.tensor_algebra.basic
import algebra.category.Module.abelian

import .ses

universes u v

open category_theory category_theory.limits

variables (R : Type u) [comm_ring R] (a b : ses (Module.{u} R)) (f : a ⟶ b)

def connecting : kernel f.vr ⟶ cokernel f.vl :=
sorry
