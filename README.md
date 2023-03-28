# Equivalent definitions of flatness

## Results in this repo

For $R$ any commutative ring and $M$ an $R$-module,

- let $S$ be a commutative ring and assume $M$ is an $R,S$-bimodule, then $(- \otimes M) \dashv \mathrm{Hom}(M, -)$ as functors between $R$-mods to $S$-mods. See [`adjunction_general.lean`](src/adjunction_general.lean#L363). This also gives some small things like how to construct group homomorphisms $M \otimes_R N \to G$ where $G$ is some abelian group.

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

1. in terms of short exact sequences:

```lean
variables (R : Type u) [comm_ring R] 
variables (M : Type u) [add_comm_group M] [module R M]

protected def ses : Prop := 
(tensor_right (Module.of R M)).is_exact

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

5. in terms of preserving exactness:

```lean
protected def exact : Prop :=
∀ ⦃N1 N2 N3 : Module.{u} R⦄ (l12 : N1 ⟶ N2) (l23 : N2 ⟶ N3)
  (he : exact l12 l23),
  exact ((tensor_right $ Module.of R M).map l12)
    ((tensor_right $ Module.of R M).map l23)
```

6. in terms of vanishing higher torsions:

```lean
def higher_Tor'_zero_of_flat (h : module.flat.exact R M) : 
  ∀ (n : ℕ) (hn : 0 < n) (N : Module.{u} R), 
    ((Tor' (Module.{u} R) n).obj N).obj M ≅ 0 :=
```

7. in terms of the first torsion:

```lean
def first_Tor'_zero_of_flat (h : module.flat.exact R M) :
  ∀ (N : Module.{u} R), ((Tor' (Module.{u} R) 1).obj N).obj M ≅ 0 :=
```

8. in terms of the first torsion of ideals:

```lean
def first_Tor'_ideal_zero_of_flat (h : module.flat.exact R M) :
  ∀ (I : ideal R), ((Tor' (Module.{u} R) 1).obj (Module.of R (R ⧸ I))).obj M ≅ 0 :=
```

9. in terms of the first torsion of finitely generated ideals:

```lean
def first_Tor'_fg_ideal_zero_of_flat (h : module.flat.exact R M) :
  ∀  (I : ideal R) (hI : I.fg), 
    ((Tor' (Module.{u} R) 1).obj (Module.of R (R ⧸ I))).obj M ≅ 0 :=
```

Since tensoring is right exact, the equivalence between definition 1 and definition 2 is not hard to see. Using a lemma due to [Lambeck](doc/Lambek.pdf) that [injectivity of $M^*$ implies its flatness](src/flat.lean#117), one can see that [3 implies 2](src/flat.lean#204). Using a colimit argument, one can see that [4 implies 3](src/flat.lean#214). Other directions of implications are all easy. Thus the four definitions are [equivalent](src/flat.lean#223). This is [00HD from the stack project](https://stacks.math.columbia.edu/tag/00HD).

## Things that are not great

- Naming and documentation.

- Universe level: $R$ and $M$ must be in the same universe. This is because we are later considering $I \otimes M \to R \otimes M$, so it makes sense to let $I, R, M$ be in the same universe. This in principle can be generalized to $R : \mathsf{Type}_u$ and $M : \mathsf{Type}_{\mathrm{max}(u, v)}$.

## Some homological algebra that somehow ended up in this repository

We can consider homological bicomplexes indexed by either natural numbers or integers (or maybe even $\mathbb Z_n$ for shorter complexes) and the arrows can be either up or down (homology or cohomology). Below is an example where the indexing set is integers and arrows are going up (going from smaller number to bigger numbers). We want to collapse a double complex $(C_{i, j}, d_h, d_v)$ into a single complex $\operatorname{Tot}^{\oplus}_k := \bigoplus_{i+j = k}C_{i, j}$ with differential $d^{\oplus} = d_h + d_v$. For this to be a differential, the bicomplex need to have anticommutative squares (i.e. $d_hd_v + d_vd_h = 0$).
$$
\begin{CD}
@. \cdots @.\cdots @.\cdots\\
@. @VVV @VVV @VVV \\
\cdots @>>> C_{-1,0} @>{d_h}>>C_{-1, 1} @>{d_h}>> C_{-1, 2} @>>>\cdots\\
@. @V{d_v}VV @V{d_v}VV @V{d_v}VV\\
\cdots @>>> C_{0,0} @>{d_h}>> C_{0, 1} @>{d_h}>> C_{0, 2} @>>>\cdots\\
@. @V{d_v}VV @V{d_v}VV @V{d_v}VV\\
\cdots @>>> C_{1,0} @>{d_h}>> C_{1, 1} @>{d_h}>> C_{1,2} @>>> \cdots\\
@. @VVV @VVV @VVV \\
@. \cdots @. \cdots @. \cdots
\end{CD}
$$

The only issue is that we don't want to keep repeating for different indexing sets and different directions of arrows. So we generalize to allow the homological bicomplex to have a row shape $a$ indexed by $\alpha$ and a column shape $b$ indexed by $\beta$. Then we collect $\operatorname{Tot}^{\oplus}$ using a new shape $c$ on $\gamma$. To achieve this, we need a heterogeneous addition function $(+) : \alpha \to \beta \to \gamma$ such that

- for all $i, i' \in \alpha$ and $j \in \beta$, $i \to_a i'$ if and only if $i + j \to_c i' + j$;
- for all $j, j' \in \beta$ and $i \in \alpha$, $j \to_b j'$ if and only if $i+j\to_c i + j'$;
- addition is cancellative on both input: $i + j = i' + j$ if and only if $i = i'$ and $i + j = i + j'$ if and only if $j = j'$;
- if $i+j\to_c k \to_c \operatorname{succ}(i) + \operatorname{succ}(j)$ then $k$ is equal to both $\operatorname{succ}(i) + j$ and $i + \operatorname{succ}(j)$;

and the shapes $a, b, c$ must all be irreflexive. Then the total differential $\bigoplus_{i+j=k}\to \bigoplus_{m+n=k'}$ is defined to be the linear map whose $(i,j)$-th projection is
$$
\sum_{m=i~\mathrm{or}~n=j}\left(C_{i,j}\stackrel{D}{\to} C_{m,n}\hookrightarrow\bigoplus_{m+n=k}\right),
$$
where
$$
D =\left\{
\begin{aligned}
d_h & & i = j \\
d_v & & m = n \\
0 & & \text{otherwise}
\end{aligned}\right..
$$

## Acknowledgment

The proof of equivalent definitions of flatness here is an adaptation of an outline due to Andrew Yang (@erdOne) on Zulip. Long exact sequences and snake lemma are taken from LTE. The generalization of collapsing double complexes into its total complex is inspired by Professor Kevin Buzzard.
