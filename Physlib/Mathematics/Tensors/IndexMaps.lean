/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Tensor
/-!

# Maps at the indices of tensors

Maps of tensors at one index, such as lowering an index with a metric.

## i. Overview

An operation on one index of a tensor, such as lowering it, is a linear map applied at that index.
Such a map is Mathlib's `PiTensorProduct.map` of one linear map per index, so it is linear, and two
maps at the same index compose index by index.

The example is lowering the first index of a Lorentz tensor `T^μν` with the Minkowski metric. The
metric gives the map `v^μ ↦ v_μ = η_μρ v^ρ` from vectors to covectors, and lowering applies it at
the first index, `T_μ^ν = η_μρ T^ρν`. The color of that index changes from up to down, and the
other index is untouched.

For the result to transform as a tensor, the map must commute with the group. Acting by `Λ` and
then applying the map gives the same as applying the map and then acting by `Λ`. A linear map with
this property is an intertwining map. The metric gives one because `Λᵀ η Λ = η`.

`linearMapAt i f h` applies a linear map `f` at the index `i` (A). It is `PiTensorProduct.map` of
the family `indexMapsAt i f h`, which is `f` at `i` and `S.cast` at every other index. The cast
keeps the vector and changes only its type, from the color `c x` to the equal color `c' x`, using
`h`. When `f` is an intertwining map, so is `linearMapAt i f h`, and it is `intertwiningMapAt`.

When `f` is an equivalence of representations, so is the map at one index, `congrAt` (B). Raising
the index is then the inverse of lowering it (`congrAt_symm`).

The components after a map at one index are a sum over the labels at that index (C). In the
example this is `T_μ^ν = ∑ ρ, η_μρ T^ρν`, where `updateBasisIdx` puts `ρ` at the first index.

## ii. Key results

- `Species.linearMapAt`, `Species.intertwiningMapAt` and `Species.congrAt` : a linear map, an
  intertwining map, or an equivalence of representations, applied at one index.
- `Species.tensorBasis_repr_linearMapAt` : the components of a tensor after `linearMapAt`, with
  `Species.updateBasisIdx` : the labels `φ` with `ρ` at the index `i`.

## iii. Table of contents

- A. A map at one index
- B. An equivalence of representations at one index
- C. Components

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G]

namespace Tensor

variable {ι : Type} {c : ι → Color K}

namespace Species

variable {S : Species k G K}

variable {c' : ι → Color K}

/-!

## A. A map at one index

`linearMapAt i f h` applies `f` at the index `i`, `u ⊗ v ↦ u ⊗ f v`. The map `f` may change
the color at `i`, as lowering turns `⟨vec, up⟩` into `⟨vec, down⟩`. The proof `h` says that the
other colors stay the same, and the vectors there move by `S.cast`.

-/

variable [DecidableEq ι]

variable (S) in
/-- The family of linear maps with `f` at the index `i` and `S.cast (h x _)` at every other
index `x`. -/
noncomputable def indexMapsAt (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : Π x, S.V (c x) →ₗ[k] S.V (c' x) :=
  fun x => if hx : x = i then hx ▸ f else (S.cast (h x hx)).toLinearMap

/-- At the index `i`, `indexMapsAt i f h` is `f`. -/
@[simp]
lemma indexMapsAt_apply_self (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : S.indexMapsAt i f h i = f :=
  dite_eq_left rfl

/-- At an index `x ≠ i`, `indexMapsAt i f h` is `S.cast (h x hx)`. -/
@[simp]
lemma indexMapsAt_apply_ne (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) {x : ι} (hx : x ≠ i) :
    S.indexMapsAt i f h x = (S.cast (h x hx)).toLinearMap :=
  dite_eq_right hx

variable (S) in
/-- The linear map `f` at the index `i` and `S.cast (h x _)` at every other index `x`,
`u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. It is Mathlib's `PiTensorProduct.map` of `indexMapsAt i f h`. -/
noncomputable def linearMapAt (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : Tensor S c →ₗ[k] Tensor S c' :=
  PiTensorProduct.map (S.indexMapsAt i f h)

/-- On a pure tensor, `linearMapAt` applies `f` to the vector at `i` and keeps the others,
`u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
lemma linearMapAt_pure (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) (p : Π x, S.V (c x)) (q : Π x, S.V (c' x))
    (hqi : q i = f (p i)) (hq : ∀ x (hx : x ≠ i), q x = S.cast (h x hx) (p x)) :
    S.linearMapAt i f h (S.pure p) = S.pure q := by
  refine (map_pure _ p).trans (congrArg S.pure (funext fun x => ?_))
  by_cases hx : x = i
  · subst hx
    simp [hqi]
  · simp [hx, hq x hx]

/-- `linearMapAt` of `f` and then of `g` at the same index is `linearMapAt` of `g ∘ₗ f`. -/
lemma linearMapAt_comp {c'' : ι → Color K} (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (g : S.V (c' i) →ₗ[k] S.V (c'' i)) (h : ∀ x, x ≠ i → c x = c' x)
    (h' : ∀ x, x ≠ i → c' x = c'' x) :
    S.linearMapAt i g h' ∘ₗ S.linearMapAt i f h =
      S.linearMapAt i (g ∘ₗ f) fun x hx => (h x hx).trans (h' x hx) := by
  refine (PiTensorProduct.map_comp _ _).symm.trans
    (congrArg PiTensorProduct.map (funext fun x => ?_))
  by_cases hx : x = i
  · subst hx
    simp
  · ext v
    simp [hx, Representation.Equiv.cast_apply]

/-- `linearMapAt` of the identity is the identity. -/
lemma linearMapAt_id (i : ι) (h : ∀ x, x ≠ i → c x = c x) :
    S.linearMapAt i LinearMap.id h = LinearMap.id :=
  ext_pure fun p => linearMapAt_pure i _ h p p rfl fun _ _ => rfl

variable (S) in
/-- The intertwining map `f` at the index `i` and `S.cast (h x _)` at every other index
`x`, `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. It is `linearMapAt` of `f`. -/
noncomputable def intertwiningMapAt (i : ι)
    (f : (S.rep (c i)).IntertwiningMap (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) : (S.tensorRep c).IntertwiningMap (S.tensorRep c') where
  toLinearMap := S.linearMapAt i f.toLinearMap h
  -- `S.tensorRep c g` is `PiTensorProduct.map` of the `S.rep (c x) g`. The check is index by index.
  isIntertwining' g := by
    refine (PiTensorProduct.map_comp _ _).symm.trans
      ((congrArg PiTensorProduct.map (funext fun x => ?_)).trans (PiTensorProduct.map_comp _ _))
    by_cases hx : x = i
    · subst hx
      simpa using f.isIntertwining' g
    · simpa [hx] using (S.cast (h x hx)).toIntertwiningMap.isIntertwining' g

/-- The linear map of `intertwiningMapAt` is `linearMapAt`. -/
lemma toLinearMap_intertwiningMapAt (i : ι) (f : (S.rep (c i)).IntertwiningMap (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) :
    (S.intertwiningMapAt i f h).toLinearMap = S.linearMapAt i f.toLinearMap h :=
  rfl

/-!

## B. An equivalence of representations at one index

Lowering the first index of `T^μν` with the metric is `congrAt` of the equivalence
`v^μ ↦ η_μρ v^ρ`. Raising it is the inverse, `congrAt` of the inverse equivalence (`congrAt_symm`).

-/

variable (S) in
/-- The equivalence of representations `f` at the index `i` and `S.cast (h x _)` at every
other index `x`. It is `intertwiningMapAt` of `f`, with inverse `intertwiningMapAt` of `f.symm`. -/
noncomputable def congrAt (i : ι) (f : (S.rep (c i)).Equiv (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) : (S.tensorRep c).Equiv (S.tensorRep c') :=
  .mk (.ofLinearMap (S.linearMapAt i f.toLinearMap h)
    (S.linearMapAt i f.symm.toLinearMap fun x hx => (h x hx).symm)
    (by rw [linearMapAt_comp, ← Representation.Equiv.toLinearMap_trans,
      Representation.Equiv.symm_trans, Representation.Equiv.toLinearMap_refl, linearMapAt_id])
    (by rw [linearMapAt_comp, ← Representation.Equiv.toLinearMap_trans,
      Representation.Equiv.trans_symm, Representation.Equiv.toLinearMap_refl, linearMapAt_id]))
    (S.intertwiningMapAt i f.toIntertwiningMap h).isIntertwining'

/-- `congrAt` is `intertwiningMapAt` of the underlying intertwining map. -/
lemma congrAt_eq_intertwiningMapAt (i : ι) (f : (S.rep (c i)).Equiv (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.congrAt i f h t = S.intertwiningMapAt i f.toIntertwiningMap h t := rfl

/-- The inverse of `congrAt` of `f` is `congrAt` of `f.symm`. -/
lemma congrAt_symm (i : ι) (f : (S.rep (c i)).Equiv (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) :
    (S.congrAt i f h).symm = S.congrAt i f.symm (fun x hx => (h x hx).symm) :=
  Representation.Equiv.ext rfl

/-!

## C. Components

`tensorBasis_repr_linearMapAt` gives the components of a tensor after a map at one index in
terms of its components before, `(ηT)_μ^ν = ∑ ρ, η_μρ T^ρν`.

A component of a tensor is given by labels `φ`, one at each index, as `(μ, ν)` chooses `T_μ^ν`.
The component of `linearMapAt i f h t` at `φ` is a sum over the labels `ρ` at the index `i`. Each
term is the matrix entry of `f` in row `φ i` and column `ρ`, times the component of `t` at `φ` with
`ρ` at the index `i`. In the example, `φ = (μ, ν)` and `i` is the first index.

`updateBasisIdx i h φ ρ` are those labels of `t`, `φ` with `ρ` at the index `i`, as `(ρ, ν)`.
The other entries keep their values, with their type moved from the colors `c'` of the new tensor
to the colors `c` of `t`, which agree there by `h`.

-/

variable {basisIdx : K → Type}

/-- The basis index `φ` with `ρ` at the index `i`. Its other entries keep their values and move
from the colors `c'` to the colors `c` along `h`. -/
def updateBasisIdx (i : ι) (h : ∀ x, x ≠ i → c x = c' x) (φ : Π x, basisIdx (c' x).kind)
    (ρ : basisIdx (c i).kind) : Π x, basisIdx (c x).kind :=
  fun x => if hx : x = i then hx ▸ ρ
    else cast (congrArg (basisIdx ∘ Color.kind) (h x hx).symm) (φ x)

/-- At the index `i`, `updateBasisIdx i h φ ρ` is `ρ`. -/
@[simp]
lemma updateBasisIdx_self (i : ι) (h : ∀ x, x ≠ i → c x = c' x) (φ : Π x, basisIdx (c' x).kind)
    (ρ : basisIdx (c i).kind) : updateBasisIdx i h φ ρ i = ρ :=
  dite_eq_left rfl

/-- At an index `x ≠ i`, `updateBasisIdx i h φ ρ` is `φ x` moved along `h x hx`. -/
@[simp]
lemma updateBasisIdx_ne (i : ι) (h : ∀ x, x ≠ i → c x = c' x) (φ : Π x, basisIdx (c' x).kind)
    (ρ : basisIdx (c i).kind) {x : ι} (hx : x ≠ i) :
    updateBasisIdx i h φ ρ x = cast (congrArg (basisIdx ∘ Color.kind) (h x hx).symm) (φ x) :=
  dite_eq_right hx

/-- With the same labels `β` at every kind, as `Fin 1 ⊕ Fin d` for Lorentz indices,
`updateBasisIdx i h φ ρ` is `Function.update φ i ρ`. -/
lemma updateBasisIdx_const {β : Type} (i : ι) (h : ∀ x, x ≠ i → c x = c' x) (φ : ι → β)
    (ρ : β) : updateBasisIdx (basisIdx := fun _ => β) i h φ ρ = Function.update φ i ρ := by
  funext x
  by_cases hx : x = i
  · subst hx
    simp
  · simp [hx]

variable [S.HasBasis basisIdx] [∀ κ, Fintype (basisIdx κ)]
  [∀ κ, DecidableEq (basisIdx κ)]

/-- The components of `linearMapAt i f h t` in terms of those of `t`,
`(f T)^…ν… = ∑ ρ, f^ν_ρ T^…ρ…`, with `f^ν_ρ` the matrix of `f`. -/
lemma tensorBasis_repr_linearMapAt [Fintype ι] (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (S.linearMapAt i f h t) φ = ∑ ρ : basisIdx (c i).kind,
      LinearMap.toMatrix (S.basis (c i)) (S.basis (c' i)) f (φ i) ρ *
        (S.tensorBasis c).repr t (updateBasisIdx i h φ ρ) := by
  induction t with
  | smul r t ht => simp [ht, Finset.mul_sum, mul_left_comm r]
  | add t t' ht ht' => simp [ht, ht', mul_add, Finset.sum_add_distrib]
  | pure p =>
    -- Split off the index `i`, where `f` acts, from the indices where the label is only moved.
    rw [show S.linearMapAt i f h (S.pure p) = _ from map_pure _ p, tensorBasis_repr_pure,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), indexMapsAt_apply_self,
      ← LinearMap.toMatrix_mulVec_repr (S.basis (c i)) (S.basis (c' i)),
      Matrix.mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [tensorBasis_repr_pure, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      updateBasisIdx_self, mul_assoc]
    refine congrArg _ (congrArg _ (Finset.prod_congr rfl fun x hx => ?_))
    have hx := Finset.ne_of_mem_erase hx
    rw [indexMapsAt_apply_ne _ _ _ hx, updateBasisIdx_ne _ _ _ _ hx]
    exact basis_repr_cast _ _ _

end Species

end Tensor
