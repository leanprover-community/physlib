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

Many operations on tensors are built from the map at one index defined here, which commutes with
the group. A map at one index (A) changes that index and keeps the others, as lowering the index
`μ` does, `T_μ^ν = η_μρ T^ρν`, which changes its color to `⟨vec, down⟩`. Since the metric is
invertible and invariant under the group, lowering is an equivalence of representations, with
raising as its inverse (C). Contracting an index with an invariant tensor on two indices,
`T^…μ… g_μν`, is a map at that index.

Every map between tensors defined here commutes with the group, and a map that changes the color of
an index is built from a map that commutes with the group. A covector built by hand from the
components of a vector, `w_μ := v^μ`, does not commute with the group in general.
It can be written explicitly, through `coloredEquiv`
or the components in `tensorBasis`, but it cannot change a color through these maps, and it is not
lowering the index, which uses the metric.

Each map is fixed by its values on pure tensors such as `u ⊗ v`. So its laws, such as composition
and commuting with the group, are proved once here, and not again for each operation. A map at one
index acts on the components of a tensor through that index alone, `(f T)^…ν… = ∑ μ, f^ν_μ T^…μ…`
(B).

## ii. Key results

- `Species.intertwiningMapAt` and `Species.congrAt` apply an intertwining map, or an equivalence of
  representations, at one index, and `Species.tensorBasis_repr_intertwiningMapAt` gives
  the components of a tensor after `intertwiningMapAt`.

## iii. Table of contents

- A. An intertwining map at one index
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

## A. An intertwining map at one index

`intertwiningMapAt i f h` applies an intertwining map `f` at the index `i` and keeps the others,
`u ⊗ v ↦ u ⊗ f v`. The map `f` may change the color at `i`, as lowering turns `⟨vec, up⟩` into
`⟨vec, down⟩`. So the result has other colors `c'`, and `h : ∀ x, x ≠ i → c x = c' x` says that
they agree with `c` at the other indices. There the vectors are moved along `h` by `S.cast`.
`indexMapsAt i f h` is the family with `f` at `i` and `S.cast` elsewhere, and `intertwiningMapAt` is
Mathlib's `PiTensorProduct.map` of it. Contracting with an invariant tensor `g` on two indices is
`intertwiningMapAt` of `g` read as a linear map, which commutes with the group because `g` is
invariant.

-/

variable [DecidableEq ι]

variable (S) in
/-- The family of intertwining maps with `f` at the index `i` and the identity, moved along `h x`,
at every other index `x`. `intertwiningMapAt` applies it index by index. -/
noncomputable def indexMapsAt (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) :
    Π x, (S.colored.rep (c x)).IntertwiningMap (S.colored.rep (c' x)) :=
  Function.update
    (fun x => if hx : x = i then 0 else (S.colored.cast (h x hx)).toIntertwiningMap) i f

/-- At the index `i`, `indexMapsAt i f h` is `f`. -/
@[simp]
lemma indexMapsAt_apply_self (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) : S.indexMapsAt i f h i = f :=
  Function.update_self _ _ _

/-- At an index `x ≠ i`, `indexMapsAt i f h` is `S.colored.cast (h x hx)`. -/
@[simp]
lemma indexMapsAt_apply_ne (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) {x : ι} (hx : x ≠ i) :
    S.indexMapsAt i f h x = (S.colored.cast (h x hx)).toIntertwiningMap := by
  rw [indexMapsAt, Function.update_of_ne hx, dite_eq_right hx]

/-- A family with `f` at the index `i` and the moves along `h x` at the other indices is
`indexMapsAt i f h`. -/
lemma eq_indexMapsAt
    {F : Π x, (S.colored.rep (c x)).IntertwiningMap (S.colored.rep (c' x))} (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (hi : F i = f)
    (hne : ∀ x (hx : x ≠ i), F x = (S.colored.cast (h x hx)).toIntertwiningMap) :
    F = S.indexMapsAt i f h :=
  Function.eq_update_iff.2 ⟨hi, fun x hx => by rw [hne x hx, dite_eq_right hx]⟩

variable (S) in
/-- The intertwining map `f` at the index `i`, and the identity, moved along `h x`, at every other
index `x`, as in `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. It is Mathlib's `PiTensorProduct.map` of
`indexMapsAt i f h`, and it commutes with the group because every map of the family does. -/
noncomputable def intertwiningMapAt (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) : (S.tensorRep c).IntertwiningMap (S.tensorRep c') :=
  ⟨PiTensorProduct.map fun x => (S.indexMapsAt i f h x).toLinearMap, fun g => LinearMap.ext
    ((Representation.IsIntertwiningMap.piTprodMap fun x =>
      ⟨(S.indexMapsAt i f h x).isIntertwining⟩).isIntertwining g)⟩

/-- On a pure tensor, `intertwiningMapAt` applies `S.indexMapsAt i f h x` to the vector at each
index `x`. -/
lemma intertwiningMapAt_pure_indexMapsAt (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (p : Π x, S.colored.V (c x)) :
    S.intertwiningMapAt i f h (S.pure p) = S.pure fun x => S.indexMapsAt i f h x (p x) :=
  PiTensorProduct.map_tprod _ _

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
  · rw [indexMapsAt_apply_ne _ _ _ hx, hq x hx]
    rfl

/-- `intertwiningMapAt` of `f` and then of `g` at the same index is `intertwiningMapAt` of
`g.comp f`. -/
lemma intertwiningMapAt_comp {c'' : ι → Color K} (i : ι)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (g : (S.colored.rep (c' i)).IntertwiningMap (S.colored.rep (c'' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (h' : ∀ x, x ≠ i → c' x = c'' x) :
    (S.intertwiningMapAt i g h').comp (S.intertwiningMapAt i f h) =
      S.intertwiningMapAt i (g.comp f) fun x hx => (h x hx).trans (h' x hx) :=
  Representation.IntertwiningMap.ext <| ext_pure fun p => by
    change S.intertwiningMapAt i g h' (S.intertwiningMapAt i f h (S.pure p)) =
      S.intertwiningMapAt i (g.comp f) _ (S.pure p)
    rw [intertwiningMapAt_pure_indexMapsAt, intertwiningMapAt_pure_indexMapsAt,
      intertwiningMapAt_pure_indexMapsAt]
    refine congrArg S.pure (funext fun x => ?_)
    by_cases hx : x = i
    · subst hx
      simp
    · simp [hx]

/-- `intertwiningMapAt` of the identity is the identity. -/
lemma intertwiningMapAt_id (i : ι) (h : ∀ x, x ≠ i → c x = c x := fun _ _ => rfl) :
    S.intertwiningMapAt i (.id _) h = .id _ :=
  Representation.IntertwiningMap.ext <| ext_pure fun p =>
    intertwiningMapAt_pure i _ h p p rfl fun _ _ => rfl

/-!

## B. Components

In components, `intertwiningMapAt` acts on the one index, `(f T)^…ν… = ∑ μ, f^ν_μ T^…μ…`
(`tensorBasis_repr_intertwiningMapAt`).

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
      ← Representation.IntertwiningMap.toLinearMap_apply,
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
