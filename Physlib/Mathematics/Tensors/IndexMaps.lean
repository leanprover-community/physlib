/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Tensor
/-!

# Maps at the indices of tensors

Maps of tensors at every index or at one index, such as lowering an index with a metric.

## i. Overview

Many operations on tensors are built from two kinds of linear map defined here. A map at every index
(A) acts on each index, as a Lorentz transformation does, `(ΛT)^μν = Λ^μ_σ Λ^ν_τ T^στ`, by the
representation of the color of each index. A map at one index (B) changes that index and keeps the
others, as lowering the index `μ` with the metric does, `T_μ^ν = η_μρ T^ρν`, which changes its color
to `⟨vec, down⟩`. Since the metric is invertible and invariant under the group, lowering is an
equivalence of representations, with raising as its inverse (D). Reindexing uses the map at every
index, and contracting an index with a tensor on two indices, `T^…μ… F_μ^ν`, is a map at that index.

Each map is fixed by its values on pure tensors such as `u ⊗ v`. So its laws, such as composition
and commuting with the group, are proved once here, and not again for each operation. A map at one
index acts on the components of a tensor through that index alone, `(f T)^…ν… = ∑ μ, f^ν_μ T^…μ…`
(C).

## ii. Key results

- `Species.mapIndices` applies a map at every index.
- `Species.mapAt` and `Species.congrAt` apply a map at one index, and
  `Species.tensorBasis_repr_mapAt` gives `mapAt` in components.

## iii. Table of contents

- A. A linear map at every index
- B. A linear map at one index
- C. Components
- D. An equivalence of representations at one index

## iv. References

* None.

-/

@[expose] public section

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

namespace Tensor

variable {ι : Type} {c : ι → Color K}

namespace Species

variable {S : Species k G K basisIdx}

/-!

## A. A linear map at every index

`mapIndices f` applies a linear map `f x` at every index `x`, `u ⊗ v ↦ f₀ u ⊗ f₁ v`. It is
Mathlib's `PiTensorProduct.map`, and it commutes with the group when every `f x` does
(`mapIndices_smul`).

-/

variable {c' : ι → Color K}

variable (S) in
/-- A linear map `f x` at every index `x`, as in `u ⊗ v ↦ f₀ u ⊗ f₁ v`. It is Mathlib's
`PiTensorProduct.map`. -/
noncomputable def mapIndices (f : Π x, S.colored.V (c x) →ₗ[k] S.colored.V (c' x)) :
    Tensor S c →ₗ[k] Tensor S c' :=
  PiTensorProduct.map f

/-- On a pure tensor, `mapIndices` applies `f x` to the vector at each index `x`. -/
@[simp]
lemma mapIndices_pure (f : Π x, S.colored.V (c x) →ₗ[k] S.colored.V (c' x))
    (p : Π x, S.colored.V (c x)) :
    S.mapIndices f (S.pure p) = S.pure fun x => f x (p x) :=
  PiTensorProduct.map_tprod _ _

/-- Two index-wise maps in sequence are the index-wise map of the composites. -/
lemma mapIndices_comp {c'' : ι → Color K} (f : Π x, S.colored.V (c x) →ₗ[k] S.colored.V (c' x))
    (g : Π x, S.colored.V (c' x) →ₗ[k] S.colored.V (c'' x)) :
    S.mapIndices g ∘ₗ S.mapIndices f = S.mapIndices fun x => g x ∘ₗ f x :=
  (PiTensorProduct.map_comp g f).symm

/-- Two index-wise maps in sequence are the index-wise map of the composites, on a tensor. -/
@[simp]
lemma mapIndices_mapIndices {c'' : ι → Color K}
    (f : Π x, S.colored.V (c x) →ₗ[k] S.colored.V (c' x))
    (g : Π x, S.colored.V (c' x) →ₗ[k] S.colored.V (c'' x)) (t : Tensor S c) :
    S.mapIndices g (S.mapIndices f t) = S.mapIndices (fun x => g x ∘ₗ f x) t :=
  LinearMap.congr_fun (mapIndices_comp f g) t

/-- The index-wise map of the identities is the identity. -/
lemma mapIndices_id : S.mapIndices (c := c) (fun _ => LinearMap.id) = LinearMap.id :=
  PiTensorProduct.map_id

/-- The index-wise map of the identities is the identity, on a tensor. -/
@[simp]
lemma mapIndices_id_apply (t : Tensor S c) : S.mapIndices (fun _ => LinearMap.id) t = t :=
  LinearMap.congr_fun mapIndices_id t

/-- Linear maps that commute with the group action at every index commute with it on tensors,
`f (Λ T) = Λ f T`. -/
lemma mapIndices_smul {f : Π x, S.colored.V (c x) →ₗ[k] S.colored.V (c' x)}
    (hf : ∀ x g v, f x (S.colored.rep (c x) g v) = S.colored.rep (c' x) g (f x v)) (g : G)
    (t : Tensor S c) :
    S.mapIndices f (g • t) = g • S.mapIndices f t :=
  (Representation.IsIntertwiningMap.piTprodMap fun x => ⟨hf x⟩).isIntertwining g t

/-!

## B. A linear map at one index

`mapAt i f h` applies a linear map `f` at the index `i` and keeps the others, `u ⊗ v ↦ u ⊗ f v`. The
map `f` may change the color at `i`, as lowering turns `⟨vec, up⟩` into `⟨vec, down⟩`. So the result
has other colors `c'`, and `h : ∀ x, x ≠ i → c x = c' x` says that they agree with `c` at the other
indices. There the vectors are moved along `h` by `S.cast`. `indexMapsAt i f h` is the family with
`f` at `i` and `S.cast` elsewhere, and `mapAt` is `mapIndices` of it. Contracting with a tensor `F`
on two indices is `mapAt` of `F` read as a linear map.

-/

variable [DecidableEq ι]

variable (S) in
/-- The family of linear maps with `f` at the index `i` and the identity, moved along `h x`, at
every other index `x`. `mapAt` applies it index by index. -/
noncomputable def indexMapsAt (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : Π x, S.colored.V (c x) →ₗ[k] S.colored.V (c' x) :=
  Function.update (fun x => if hx : x = i then 0 else (S.colored.cast (h x hx)).toLinearMap) i f

/-- At the index `i`, `indexMapsAt i f h` is `f`. -/
@[simp]
lemma indexMapsAt_apply_self (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : S.indexMapsAt i f h i = f :=
  Function.update_self _ _ _

/-- At an index `x ≠ i`, `indexMapsAt i f h` is `S.colored.cast (h x hx)`. -/
@[simp]
lemma indexMapsAt_apply_ne (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) {x : ι} (hx : x ≠ i) :
    S.indexMapsAt i f h x = (S.colored.cast (h x hx)).toLinearMap := by
  rw [indexMapsAt, Function.update_of_ne hx, dite_eq_right hx]

/-- A family with `f` at the index `i` and the moves along `h x` at the other indices is
`indexMapsAt i f h`. -/
lemma eq_indexMapsAt {F : Π x, S.colored.V (c x) →ₗ[k] S.colored.V (c' x)} (i : ι)
    (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i)) (h : ∀ x, x ≠ i → c x = c' x) (hi : F i = f)
    (hne : ∀ x (hx : x ≠ i), F x = (S.colored.cast (h x hx)).toLinearMap) :
    F = S.indexMapsAt i f h :=
  Function.eq_update_iff.2 ⟨hi, fun x hx => by rw [hne x hx, dite_eq_right hx]⟩

/-- `indexMapsAt i f h` commutes with the group action at every index when `f` does. -/
lemma indexMapsAt_rep (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x)
    (hf : ∀ g v, f (S.colored.rep (c i) g v) = S.colored.rep (c' i) g (f v)) (x : ι) (g : G)
    (v : S.colored.V (c x)) : S.indexMapsAt i f h x (S.colored.rep (c x) g v) =
      S.colored.rep (c' x) g (S.indexMapsAt i f h x v) := by
  by_cases hx : x = i
  · subst hx
    simpa using hf g v
  · simpa [hx] using cast_rep (h x hx) g v

variable (S) in
/-- The linear map `f` at the index `i`, and the identity, moved along `h x`, at every other index
`x`, as in `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
noncomputable def mapAt (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : Tensor S c →ₗ[k] Tensor S c' :=
  S.mapIndices (S.indexMapsAt i f h)

/-- On a pure tensor, `mapAt` applies `f` to the vector at `i` and keeps the others,
`u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
lemma mapAt_pure (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) (p : Π x, S.colored.V (c x)) (q : Π x, S.colored.V (c' x))
    (hqi : q i = f (p i)) (hq : ∀ x (hx : x ≠ i), q x = S.colored.cast (h x hx) (p x)) :
    S.mapAt i f h (S.pure p) = S.pure q := by
  rw [mapAt, mapIndices_pure]
  refine congrArg S.pure (funext fun x => ?_)
  by_cases hx : x = i
  · subst hx
    rw [indexMapsAt_apply_self, hqi]
  · rw [indexMapsAt_apply_ne _ _ _ hx, hq x hx]
    rfl

/-- `mapAt` of `f` and then of `g` at the same index is `mapAt` of `g ∘ₗ f`. -/
lemma mapAt_comp {c'' : ι → Color K} (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (g : S.colored.V (c' i) →ₗ[k] S.colored.V (c'' i)) (h : ∀ x, x ≠ i → c x = c' x)
    (h' : ∀ x, x ≠ i → c' x = c'' x) :
    S.mapAt i g h' ∘ₗ S.mapAt i f h = S.mapAt i (g ∘ₗ f) fun x hx => (h x hx).trans (h' x hx) := by
  rw [mapAt, mapAt, mapAt, mapIndices_comp]
  refine congrArg _ (eq_indexMapsAt i _ _ (by simp) fun x hx => LinearMap.ext fun v => ?_)
  simp [hx]

/-- `mapAt` of the identity is the identity. -/
lemma mapAt_id (i : ι) (h : ∀ x, x ≠ i → c x = c x := fun _ _ => rfl) :
    S.mapAt i LinearMap.id h = LinearMap.id := by
  rw [mapAt, ← eq_indexMapsAt (F := fun _ => LinearMap.id) i _ h rfl
    fun _ _ => LinearMap.ext fun _ => rfl, mapIndices_id]

/-!

## C. Components

In components, `mapAt` acts on the one index, `(f T)^…ν… = ∑ μ, f^ν_μ T^…μ…`
(`tensorBasis_repr_mapAt`).

-/

/-- `mapAt` in components, `(f T)^…ν… = ∑ μ, f^ν_μ T^…μ…`, with `f^ν_μ` the matrix of `f`. -/
lemma tensorBasis_repr_mapAt [Fintype ι] (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) (φ : Π x, basisIdx (c' x).kind)
    (ψ : Π x, basisIdx (c x).kind)
    (hψ : ∀ x (hx : x ≠ i), ψ x = cast (congrArg (basisIdx ∘ Color.kind) (h x hx).symm) (φ x)) :
    (S.tensorBasis c').repr (S.mapAt i f h t) φ = ∑ μ : basisIdx (c i).kind,
      LinearMap.toMatrix (S.colored.basis (c i)) (S.colored.basis (c' i)) f (φ i) μ *
        (S.tensorBasis c).repr t (Function.update ψ i μ) := by
  induction t using induction_on_pure with
  | hsmul r t ht =>
    simp only [map_smul, Finsupp.smul_apply, ht, smul_eq_mul, Finset.mul_sum, mul_left_comm r]
  | hadd t t' ht ht' =>
    simp only [map_add, Finsupp.add_apply, ht, ht', mul_add, Finset.sum_add_distrib]
  | h p =>
    -- Split off the index `i`, where `f` acts, from the indices where the label is only moved.
    rw [mapAt, mapIndices_pure, tensorBasis_repr_pure,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), indexMapsAt_apply_self,
      ← LinearMap.toMatrix_mulVec_repr (S.colored.basis (c i)) (S.colored.basis (c' i)),
      Matrix.mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [tensorBasis_repr_pure, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Function.update_self, mul_assoc]
    refine congrArg _ (congrArg _ (Finset.prod_congr rfl fun x hx => ?_))
    have hx := Finset.ne_of_mem_erase hx
    rw [indexMapsAt_apply_ne _ _ _ hx, Function.update_of_ne hx, hψ x hx]
    exact basis_repr_cast _ _ _

/-!

## D. An equivalence of representations at one index

`congrAt i f h` applies an equivalence of representations `f` at the index `i`, as `mapAt` does.
The result is again an equivalence of representations, so it commutes with the group and has an
inverse, `congrAt` of `f.symm` (`congrAt_symm`). It is built by `equivOfPure`, with the
check on pure tensors from `mapIndices_smul`. Lowering with a metric is `congrAt` of the map
`v^μ ↦ η_νμ v^μ`, and raising is its inverse.

-/

variable (S) in
/-- The equivalence of representations `f` at the index `i`, and the identity, moved along `h x`,
at every other index `x`. On a pure tensor, `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. Its linear map is `mapAt`
of `f`. -/
noncomputable def congrAt (i : ι) (f : (S.colored.rep (c i)).Equiv (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) : (S.tensorRep c).Equiv (S.tensorRep c') :=
  equivOfPure (.ofLinearMap (S.mapAt i f.toLinearMap h)
    (S.mapAt i f.symm.toLinearMap fun x hx => (h x hx).symm)
    (by rw [mapAt_comp, show f.toLinearMap ∘ₗ f.symm.toLinearMap = LinearMap.id from
      LinearMap.ext f.apply_symm_apply, mapAt_id])
    (by rw [mapAt_comp, show f.symm.toLinearMap ∘ₗ f.toLinearMap = LinearMap.id from
      LinearMap.ext f.symm_apply_apply, mapAt_id])) fun g p =>
    mapIndices_smul (indexMapsAt_rep i _ h (f.toIntertwiningMap.isIntertwining _ _)) g (S.pure p)

/-- `congrAt` is `mapAt` of the underlying linear map. -/
lemma congrAt_eq_mapAt (i : ι) (f : (S.colored.rep (c i)).Equiv (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.congrAt i f h t = S.mapAt i f.toLinearMap h t := rfl

/-- The inverse of `congrAt` of `f` is `congrAt` of `f.symm`. -/
lemma congrAt_symm (i : ι) (f : (S.colored.rep (c i)).Equiv (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) :
    (S.congrAt i f h).symm = S.congrAt i f.symm (fun x hx => (h x hx).symm) :=
  Representation.Equiv.ext rfl

end Species

end Tensor
