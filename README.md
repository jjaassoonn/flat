# Equivalent definitions of flatness

## Results in this repo

For $R$ any commutative ring and $M$ an $R$-module,

- let $S$ be a commutative ring and assume $M$ is an $R,S$-bimodule, then $(- \otimes M) \dashv \mathrm{Hom}(M, -)$ as functors between $R$-mods to $S$-mods. See [`adjunction_general.lean`](src/adjunction_general.lean#L363).

- $- \otimes M$ is a right exact functor. Right-exactness is defined in terms of short exact sequences. See [`right_exact.lean`](src/right_exact.lean#L194). Since $(- \otimes M)$ is left adjoint, this should be automatic, but I didn't get the categorical argument working; so I just did everything by hand.

```lean
variables (R : Type u) [comm_ring R]
variables (M : Type u) [add_comm_group M] [module R M]
variables (A B C : Module.{u} R)

variables (fAB : A ⟶ B) (fBC : B ⟶ C)
variables [e0A : exact (0 : (0 : Module.{u} R) ⟶ _) fAB] 
variables [eAB : exact fAB fBC] [eC0 : exact fBC (0 : _ ⟶ (0 : Module.{u} R))]

include fAB fBC e0A eAB eC0

lemma right_exact :
  exact 
    (by exact map fAB linear_map.id : Module.of R (A ⊗[R] M) ⟶ Module.of R (B ⊗[R] M)) 
    (by exact map fBC linear_map.id : Module.of R (B ⊗[R] M) ⟶ Module.of R (C ⊗[R] M)) ∧
  exact 
    (by exact map fBC linear_map.id : Module.of R (B ⊗[R] M) ⟶ Module.of R (C ⊗[R] M))
    (0 : _ ⟶ (0 : Module.{u} R)) :=
```

- Direct limit of modules commutes with tensor products. See [`direct_lim.lean`](src/direct_lim.lean#L99)

- If $I$ is an ideal, then $I \cong \mathrm{colim} I_\alpha$ ranging over all finitely generated $I_\alpha\le I$. And thus $I \otimes_R M \cong \mathrm{colim}(I_\alpha\otimes_R M)$ See [`ideal_and_fg_ideal.lean`](src/ideal_and_fg_ideal.lean)

## A bunch of definitions for flatness

1. in terms of short exact sequence:

```lean
variables (R : Type u) [comm_ring R] 
variables (M : Type u) [add_comm_group M] [module R M]

protected def ses : Prop :=
∀ ⦃N1 N2 N3 : Module.{u u} R⦄ (l12 : N1 ⟶ N2) (l23 : N2 ⟶ N3)
  (he1 : exact (0 : (0 : Module.{u} R) ⟶ N1) l12)
  (he2 : exact l12 l23)
  (he3 : exact l23 (0 : N3 ⟶ (0 : Module.{u} R))),
exact 
  (0 : (0 : Module.{u} R) ⟶ Module.of R (N1 ⊗[R] M))  
  (by exact tensor_product.map l12 linear_map.id : 
    Module.of R (N1 ⊗[R] M) ⟶ Module.of R (N2 ⊗[R] M)) ∧
exact 
  (by exact tensor_product.map l12 linear_map.id : 
    Module.of R (N1 ⊗[R] M) ⟶ Module.of R (N2 ⊗[R] M)) 
  (by exact tensor_product.map l23 linear_map.id : 
    Module.of R (N2 ⊗[R] M) ⟶ Module.of R (N3 ⊗[R] M)) ∧
exact
  (by exact tensor_product.map l23 linear_map.id : 
    Module.of R (N2 ⊗[R] M) ⟶ Module.of R (N3 ⊗[R] M))
  (0 : _ ⟶ 0)
```

2. in terms of preserving injective functions:

```lean
protected def inj : Prop :=
∀ ⦃N N' : Module.{u} R⦄ (L : N ⟶ N'), 
  function.injective L →
  function.injective (tensor_product.map L (linear_map.id : M →ₗ[R] M)) 
```

3. in terms of ideals:

```lean
protected def ideal : Prop :=
∀ (I : ideal R), function.injective (tensor_embedding M I)
```

4. in terms of finitely generated ideals:

```lean
protected def fg_ideal : Prop :=
∀ (I : ideal R), I.fg → function.injective (tensor_embedding M I)
```

Since tensoring is right exact, the equivalence between definition 1 and definition 2 is not hard to see. Using a lemma due to [Lambeck](doc/Lambek.pdf) that [injectivity of $M^*$ implies its flatness](src/flat.lean#117), one can see that [3 implies 2](src/flat.lean#204). Using a colimit argument, one can see that [4 implies 3](src/flat.lean#214). Other direction of implications are all easy. Thus the four definitions are [equivalent](src/flat.lean#223).

## Acknowledgement

The proof here is an adptation of an outline due to Andrew Yang (@erdOne) on Zulip.
