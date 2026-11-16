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

We express operations on the indices of tensors, such as lowering an index, as linear maps. Mathlib
then composes them and distributes them over linear combinations. No proof has to be repeated in
components.

For such an operation to respect how tensors transform, its map must commute with the group.
Acting by `Λ` and then applying the map gives the same tensor as applying the map and then acting
by `Λ`. A linear map with this property is an intertwining map.

For example, lowering an index uses the map from vectors to covectors given by a metric. It
commutes with the group when the metric is invariant. The Minkowski metric gives
`v^μ ↦ v_μ = η_μν v^ν`. Since `Λᵀ η Λ = η`, lowering the transformed vector `Λv` gives the
transformed covector.

We define maps at one index (A). Most operations act at one index and keep the others, as lowering
`μ` does, `T_μ^ν = η_μρ T^ρν`. `intertwiningMapAt i f h` is `PiTensorProduct.map` of the family
`indexMapsAt i f h`, since Mathlib's `PiTensorProduct.map` needs one linear map for each index. The
family is `f` at the index `i` and `S.colored.cast` at every other index. The cast keeps the vector
and changes only its type, from the color `c x` to the equal color `c' x`, using `h`. Maps at two
different indices commute (`intertwiningMapAt_comm`), so two indices can be lowered in either order.

We then make a map at one index an equivalence when `f` is one (B). Raising an index is then the
inverse of lowering it (`congrAt_symm`). Finally we give the components of a tensor after a map at
one index (C), `(f T)^…ν… = ∑ ρ, f^ν_ρ T^…ρ…`.

## ii. Key results

- `Species.intertwiningMapAt` and `Species.congrAt` apply an intertwining map, or an equivalence of
  representations, at one index, and `Species.tensorBasis_repr_intertwiningMapAt` gives
  the components of a tensor after `intertwiningMapAt`.
- `Species.intertwiningMapAt_comm` proves that maps at two different indices commute, also when they
  change the colors.

## iii. Table of contents

- A. A map at one index
- B. An equivalence of representations at one index
- C. Components

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

/-- Intertwining maps at two different indices commute, also when they change the colors. Lowering
`μ` and `ν` of `T^μν` in either order gives `T_μν`. The maps `g'` and `f'` are `g` and
`f` moved along the colors the other map keeps (`hff'`, `hgg'`, `rfl` by default). Use it as a
term, as in `intertwiningMapAt_comm hij ..`. -/
lemma intertwiningMapAt_comm {c₁ c₂ c₃ : ι → Color K} {i j : ι} (hij : i ≠ j)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c₁ i)))
    (g : (S.colored.rep (c₁ j)).IntertwiningMap (S.colored.rep (c₃ j)))
    (g' : (S.colored.rep (c j)).IntertwiningMap (S.colored.rep (c₂ j)))
    (f' : (S.colored.rep (c₂ i)).IntertwiningMap (S.colored.rep (c₃ i)))
    (hf : ∀ x, x ≠ i → c x = c₁ x) (hg : ∀ x, x ≠ j → c₁ x = c₃ x)
    (hg' : ∀ x, x ≠ j → c x = c₂ x) (hf' : ∀ x, x ≠ i → c₂ x = c₃ x)
    (hff' : ∀ v, f' (S.colored.cast (hg' i hij) v) = S.colored.cast (hg i hij) (f v) := by
      intro; rfl)
    (hgg' : ∀ v, g (S.colored.cast (hf j hij.symm) v) =
      S.colored.cast (hf' j hij.symm) (g' v) := by intro; rfl) :
    (S.intertwiningMapAt j g hg).comp (S.intertwiningMapAt i f hf) =
      (S.intertwiningMapAt i f' hf').comp (S.intertwiningMapAt j g' hg') :=
  Representation.IntertwiningMap.ext <| ext_pure fun p => by
    change S.intertwiningMapAt j g hg (S.intertwiningMapAt i f hf (S.pure p)) =
      S.intertwiningMapAt i f' hf' (S.intertwiningMapAt j g' hg' (S.pure p))
    simp only [intertwiningMapAt_pure_indexMapsAt]
    refine congrArg S.pure (funext fun x => ?_)
    by_cases hxi : x = i
    · subst hxi
      rw [indexMapsAt_apply_self, indexMapsAt_apply_ne _ _ _ hij, indexMapsAt_apply_ne _ _ _ hij,
        indexMapsAt_apply_self]
      exact (hff' _).symm
    by_cases hxj : x = j
    · subst hxj
      rw [indexMapsAt_apply_self, indexMapsAt_apply_ne _ _ _ hxi, indexMapsAt_apply_ne _ _ _ hxi,
        indexMapsAt_apply_self]
      exact hgg' _
    · simp [hxi, hxj]

/-!

## B. An equivalence of representations at one index

Lowering with a metric is `congrAt` of `v^μ ↦ v_ν = η_νμ v^μ`. Raising is its inverse
(`congrAt_symm`).

-/

variable (S) in
/-- The equivalence of representations `f` at the index `i` and `S.colored.cast (h x _)` at every
other index `x`. It is `intertwiningMapAt` of `f`, with inverse `intertwiningMapAt` of `f.symm`. -/
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

/-!

## C. Components

`tensorBasis_repr_intertwiningMapAt` gives the components of a tensor after a map at one index, in
terms of its components before. Lowering `μ` gives `(ηT)_μ^ν = ∑ ρ, η_μρ T^ρν`.

A component of a tensor is given by a basis index `φ`. It chooses one basis vector at each index,
as `(μ, ν)` chooses `T_μ^ν`. The component of `intertwiningMapAt i f h t` at `φ` is a sum over the
basis vectors `ρ` at the index `i`. Each term is the matrix entry of `f` in row `φ i` and column
`ρ`, times the component of `t` at `φ` with `ρ` at the index `i`. In the example, `φ = (μ, ν)`, the
index `i` is the first one, the matrix of `f` is `η`, and the component of `t` is `T^ρν`.

`updateBasisIdx i h φ ρ` is this basis index of `t`. It is `φ` with `ρ` at the index `i`. Its other
entries keep their values. Their type changes from the colors `c'` of the new tensor to the colors
`c` of `t`, which agree there by `h`.

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

end Species

end Tensor
