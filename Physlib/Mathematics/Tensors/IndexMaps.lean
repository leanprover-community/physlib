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

A map at one index (A) changes that index and keeps the others, as lowering the index `μ` does,
`T_μ^ν = η_μρ T^ρν`. `intertwiningMapAt` applies an intertwining map at one index, so that the
tensor it returns transforms by its new colors. When the map at the index is an equivalence of
representations, so is the map of tensors (C). Each map is fixed by its values
on pure tensors such as `u ⊗ v`, so its laws, such as composition and commuting with the group, are
proved once here. The maps live in the namespace `Tensor.Species` and are written with dot
notation, as `S.intertwiningMapAt`.

Every map defined here commutes with the group, so a color changes through these maps only by a
map that commutes with the group. The copy `w_μ := v^μ` of components does not, and it is not
lowering, which uses the metric.

## ii. Key results

- `Species.intertwiningMapAt` and `Species.congrAt` apply an intertwining map, or an equivalence of
  representations, at one index, and `Species.tensorBasis_repr_intertwiningMapAt` gives
  the components of a tensor after `intertwiningMapAt`.

## iii. Table of contents

- A. A map at one index
- B. Components
- C. An equivalence of representations at one index

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

variable {c' : ι → Color K}

/-!

## A. A map at one index

`intertwiningMapAt i f h` applies `f` at the index `i`, `u ⊗ v ↦ u ⊗ f v`. The map `f` may change
the color at `i`, as lowering turns `⟨vec, up⟩` into `⟨vec, down⟩`. The proof `h` says that the
other colors stay the same. At those indices the vectors move by `S.colored.cast`.

-/

variable [DecidableEq ι]

variable (S) in
/-- The family of linear maps with `f` at the index `i` and `S.colored.cast (h x _)` at every other
index `x`. -/
noncomputable def indexMapsAt (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : Π x, S.colored.V (c x) →ₗ[k] S.colored.V (c' x) :=
  fun x => if hx : x = i then hx ▸ f else (S.colored.cast (h x hx)).toLinearMap

/-- At the index `i`, `indexMapsAt i f h` is `f`. -/
@[simp]
lemma indexMapsAt_apply_self (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : S.indexMapsAt i f h i = f :=
  dite_eq_left rfl

/-- At an index `x ≠ i`, `indexMapsAt i f h` is `S.colored.cast (h x hx)`. -/
@[simp]
lemma indexMapsAt_apply_ne (i : ι) (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) {x : ι} (hx : x ≠ i) :
    S.indexMapsAt i f h x = (S.colored.cast (h x hx)).toLinearMap :=
  dite_eq_right hx

variable (S) in
/-- The intertwining map `f` at the index `i` and `S.colored.cast (h x _)` at every other index
`x`, `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
noncomputable def intertwiningMapAt (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) : (S.tensorRep c).IntertwiningMap (S.tensorRep c') where
  toLinearMap := PiTensorProduct.map (S.indexMapsAt i f.toLinearMap h)
  isIntertwining' g := ext_pure fun p => by
    change PiTensorProduct.map (S.indexMapsAt i f.toLinearMap h) (g • S.pure p) =
      g • show Tensor S c' from PiTensorProduct.map (S.indexMapsAt i f.toLinearMap h) (S.pure p)
    rw [smul_pure, map_pure, map_pure, smul_pure]
    refine congrArg S.pure (funext fun x => ?_)
    by_cases hx : x = i
    · subst hx
      simpa using Representation.IntertwiningMap.isIntertwining _ _ f g (p x)
    · simpa [hx] using Representation.IntertwiningMap.isIntertwining _ _
        (S.colored.cast (h x hx)).toIntertwiningMap g (p x)

/-- On a pure tensor, `intertwiningMapAt` applies `S.indexMapsAt i f.toLinearMap h x` to the
vector at each index `x`. -/
lemma intertwiningMapAt_pure_indexMapsAt (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (p : Π x, S.colored.V (c x)) :
    S.intertwiningMapAt i f h (S.pure p) =
      S.pure fun x => S.indexMapsAt i f.toLinearMap h x (p x) :=
  map_pure _ p

/-- On a pure tensor, `intertwiningMapAt` applies `f` to the vector at `i` and keeps the others,
`u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
lemma intertwiningMapAt_pure (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (p : Π x, S.colored.V (c x)) (q : Π x, S.colored.V (c' x))
    (hqi : q i = f (p i)) (hq : ∀ x (hx : x ≠ i), q x = S.colored.cast (h x hx) (p x)) :
    S.intertwiningMapAt i f h (S.pure p) = S.pure q := by
  rw [intertwiningMapAt_pure_indexMapsAt]
  refine congrArg S.pure (funext fun x => ?_)
  by_cases hx : x = i
  · subst hx
    rw [indexMapsAt_apply_self, hqi]
    rfl
  · rw [indexMapsAt_apply_ne _ _ _ hx, hq x hx]
    rfl

/-- `intertwiningMapAt` of `f` and then of `g` at the same index is `intertwiningMapAt` of
`g.comp f`. -/
lemma intertwiningMapAt_comp {c'' : ι → Color K} (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (g : (S.colored.rep (c' i)).IntertwiningMap (S.colored.rep (c'' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (h' : ∀ x, x ≠ i → c' x = c'' x) :
    (S.intertwiningMapAt i g h').comp (S.intertwiningMapAt i f h) =
      S.intertwiningMapAt i (g.comp f) fun x hx => (h x hx).trans (h' x hx) := by
  refine Representation.IntertwiningMap.ext ((PiTensorProduct.map_comp _ _).symm.trans
    (congrArg PiTensorProduct.map (funext fun x => ?_)))
  by_cases hx : x = i
  · subst hx
    simp
  · ext v
    simp [hx]

/-- `intertwiningMapAt` of the identity is the identity. -/
lemma intertwiningMapAt_id (i : ι) (h : ∀ x, x ≠ i → c x = c x := fun _ _ => rfl) :
    S.intertwiningMapAt i (.id _) h = .id _ :=
  Representation.IntertwiningMap.ext <| ext_pure fun p =>
    intertwiningMapAt_pure i _ h p p rfl fun _ _ => rfl

/-!

## B. Components

-/

/-- The basis index `φ` with `ρ` at the index `i`. Its other entries keep their values and move
from the colors `c'` to the colors `c` along `h`. -/
def updateBasisIdx (i : ι) (h : ∀ x, x ≠ i → c x = c' x) (φ : Π x, basisIdx (c' x).kind)
    (ρ : basisIdx (c i).kind) : Π x, basisIdx (c x).kind :=
  fun x => if hx : x = i then hx ▸ ρ
    else cast (congrArg (basisIdx ∘ Color.kind) (h x hx).symm) (φ x)

omit [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] in
/-- At the index `i`, `updateBasisIdx i h φ ρ` is `ρ`. -/
@[simp]
lemma updateBasisIdx_self (i : ι) (h : ∀ x, x ≠ i → c x = c' x) (φ : Π x, basisIdx (c' x).kind)
    (ρ : basisIdx (c i).kind) : updateBasisIdx i h φ ρ i = ρ :=
  dite_eq_left rfl

omit [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] in
/-- At an index `x ≠ i`, `updateBasisIdx i h φ ρ` is `φ x` moved along `h x hx`. -/
@[simp]
lemma updateBasisIdx_ne (i : ι) (h : ∀ x, x ≠ i → c x = c' x) (φ : Π x, basisIdx (c' x).kind)
    (ρ : basisIdx (c i).kind) {x : ι} (hx : x ≠ i) :
    updateBasisIdx i h φ ρ x = cast (congrArg (basisIdx ∘ Color.kind) (h x hx).symm) (φ x) :=
  dite_eq_right hx

/-- The components of `intertwiningMapAt i f h t` in terms of those of `t`,
`(f T)^…ν… = ∑ ρ, f^ν_ρ T^…ρ…`, with `f^ν_ρ` the matrix of `f`. -/
lemma tensorBasis_repr_intertwiningMapAt [Fintype ι] (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (S.intertwiningMapAt i f h t) φ = ∑ ρ : basisIdx (c i).kind,
      LinearMap.toMatrix (S.colored.basis (c i)) (S.colored.basis (c' i)) f.toLinearMap (φ i) ρ *
        (S.tensorBasis c).repr t (updateBasisIdx i h φ ρ) := by
  induction t using induction_on_pure with
  | hsmul r t ht =>
    simp only [map_smul, Finsupp.smul_apply, ht, smul_eq_mul, Finset.mul_sum, mul_left_comm r]
  | hadd t t' ht ht' =>
    simp only [map_add, Finsupp.add_apply, ht, ht', mul_add, Finset.sum_add_distrib]
  | h p =>
    -- Split off the index `i`, where `f` acts, from the indices where the label is only moved.
    rw [intertwiningMapAt_pure_indexMapsAt, tensorBasis_repr_pure,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), indexMapsAt_apply_self,
      ← LinearMap.toMatrix_mulVec_repr (S.colored.basis (c i)) (S.colored.basis (c' i)),
      Matrix.mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [tensorBasis_repr_pure, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      updateBasisIdx_self, mul_assoc]
    refine congrArg _ (congrArg _ (Finset.prod_congr rfl fun x hx => ?_))
    have hx := Finset.ne_of_mem_erase hx
    rw [indexMapsAt_apply_ne _ _ _ hx, updateBasisIdx_ne _ _ _ _ hx]
    exact basis_repr_cast _ _ _

/-!

## C. An equivalence of representations at one index

`congrAt i f h` applies an equivalence of representations `f` at the index `i`, as
`intertwiningMapAt` does. The result is again an equivalence of representations, so it has an
inverse, `congrAt` of `f.symm` (`congrAt_symm`). Lowering with a metric is `congrAt` of the map
`v^μ ↦ η_νμ v^μ`, and raising is its inverse.

-/

variable (S) in
/-- The equivalence of representations `f` at the index `i`, and `S.colored.cast (h x _)` at every
other index `x`. On a pure tensor, `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. Its intertwining map is
`intertwiningMapAt` of `f`. -/
noncomputable def congrAt (i : ι) (f : (S.colored.rep (c i)).Equiv (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) : (S.tensorRep c).Equiv (S.tensorRep c') :=
  .mk (.ofLinearMap (S.intertwiningMapAt i f.toIntertwiningMap h).toLinearMap
    (S.intertwiningMapAt i f.symm.toIntertwiningMap fun x hx => (h x hx).symm).toLinearMap
    (by
      rw [← Representation.IntertwiningMap.comp_toLinearMap, intertwiningMapAt_comp,
        show f.toIntertwiningMap.comp f.symm.toIntertwiningMap = .id _ by ext; simp,
        intertwiningMapAt_id]
      rfl)
    (by
      rw [← Representation.IntertwiningMap.comp_toLinearMap, intertwiningMapAt_comp,
        show f.symm.toIntertwiningMap.comp f.toIntertwiningMap = .id _ by ext; simp,
        intertwiningMapAt_id]
      rfl))
    (S.intertwiningMapAt i f.toIntertwiningMap h).isIntertwining'

/-- `congrAt` is `intertwiningMapAt` of the underlying intertwining map. -/
lemma congrAt_eq_intertwiningMapAt (i : ι) (f : (S.colored.rep (c i)).Equiv (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.congrAt i f h t = S.intertwiningMapAt i f.toIntertwiningMap h t := rfl

/-- The inverse of `congrAt` of `f` is `congrAt` of `f.symm`. -/
lemma congrAt_symm (i : ι) (f : (S.colored.rep (c i)).Equiv (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) :
    (S.congrAt i f h).symm = S.congrAt i f.symm (fun x hx => (h x hx).symm) :=
  Representation.Equiv.ext rfl

end Species

end Tensor
