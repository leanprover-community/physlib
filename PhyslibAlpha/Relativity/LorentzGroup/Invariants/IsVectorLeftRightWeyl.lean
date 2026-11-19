/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.Bispinors.Pauli.Basic
public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.AdjointClosed
public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.IsLeftRightWeyl
public import PhyslibAlpha.Relativity.PauliMatrices.ToTensor
/-!
# Lorentz invariants of a four-vector index and a left-right Weyl pair

Up to scale, the Pauli tensor is the only Lorentz invariant of a four-vector index and a
left-right Weyl pair.

## i. Overview

A family `T^{μ α α'}` carrying one four-vector index and one opposite-chirality Weyl pair is an
equivariant linear map `f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B`, `IsVectorLeftRightWeyl` (A). Every
Lorentz invariant in the range of `f` is a multiple of `f σ^^^`, the image of the Pauli
matrices as a tensor, the shape of the fermion kinetic term `ψ̄_{α'} σ̄^{μ α' α} ∂_μ ψ_α`. That is
`IsVectorLeftRightWeyl.exists_smul_map_pauliMatrix_add_of_invariant`, stated modulo a
Lorentz-stable submodule `S`, and packaged as `IsVectorLeftRightWeyl.invariantReductionToSpan`
(C).

It is enough that the invariant tensors of `ℂT[.up, .upL, .upR]` are the multiples of `σ^^^`
(B). Such a tensor is `fromTripleT` of an element of
`ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)`, and the invariants of that tensor product are
the line through the Pauli tensor, `ComplexVector.invariants_tprod_eq_span_pauliVal`. The
classification of the invariants of a family follows by
`TensorSpecies.IsEquivariant.invariantReductionToSpan` (C).

The Standard Model's fermion symbols are `Module.Dual`-valued, so their spinor indices are dual
Weyl indices, and a family of them is an equivariant map out of `ℂT[.up, .downR, .downL]`,
`IsVectorDualLeftRightWeyl`.
Dualising both Weyl indices, `dualWeylMap`, is an equivariant surjection from
`ℂT[.up, .upL, .upR]` carrying `σ^^^` to `σ^__`, so every invariant in the range of such a map is
a multiple of `f σ^__` (D). A family of dual components is turned into a map by
`ofDualVectorComponents` (E). A one-index Weyl family times a once-derived one of the other
chirality is such a family, the shape of the fermion kinetic term (F).

## ii. Key results

- `Lorentz.IsVectorLeftRightWeyl.exists_eq_smul_pauliMatrix_of_invariant` : the invariant
  tensors are the multiples of `σ^^^`.
- `Lorentz.IsVectorLeftRightWeyl.invariantReductionToSpan` : the invariants reduce to `f σ^^^`.
- `Lorentz.dualWeylMap` : the dualisation of the Weyl indices.
- `Lorentz.IsVectorDualLeftRightWeyl.invariantReductionToSpan` : the invariants reduce to
  `f σ^__`.
- `Lorentz.isVectorDualLeftRightWeyl_mul` : a one-index family times a once-derived one of the
  other chirality is a vector dual left-right Weyl family.

## iii. Table of contents

- A. Vector-Weyl families as equivariant maps
- B. The invariant tensors
- C. The classification of the Lorentz invariants
- D. Dual Weyl indices
- E. Maps from dual components
- F. Once-derived one-index Weyl families and their products

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C complexLorentzTensor

/-!

## A. Vector-Weyl families as equivariant maps

-/

/-- A family with a four-vector index and a left- and a right-handed Weyl index `T^{μ α α'}`,
  an equivariant linear map out of `ℂT[.up, .upL, .upR]`. -/
abbrev IsVectorLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.up, .upL, .upR] repLorentz f

namespace IsVectorLeftRightWeyl

open PauliMatrix

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B}
  (hf : IsVectorLeftRightWeyl B repLorentz f)

/-!

## B. The invariant tensors

A tensor of `ℂT[.up, .upL, .upR]` is `fromTripleT` of an element of
`ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)`, whose invariants are the line through the
Pauli tensor `ComplexVector.pauliVal`, and `fromTripleT` of that is `σ^^^`.

-/

/-- The invariant tensors with a four-vector index and a left-right Weyl pair are the multiples
  of the Pauli tensor. -/
lemma exists_eq_smul_pauliMatrix_of_invariant (t : ℂT[.up, .upL, .upR])
    (ht : ∀ g : SL(2,ℂ), g • t = t) : ∃ a : ℂ, t = a • σ^^^ := by
  obtain ⟨a, ha⟩ := TensorSpecies.Tensor.exists_eq_smul_fromTripleT_of_invariant
    (S := complexLorentzTensor) (c1 := .up) (c2 := .upL) (c3 := .upR)
    ComplexVector.invariants_tprod_eq_span_pauliVal ht
  refine ⟨a, ha.trans ?_⟩
  rw [toTensor_eq_pauli, TensorSpecies.Tensor.fromConstTriple, ComplexVector.pauli_apply_one]

/-!

## C. The classification of the Lorentz invariants

-/

include hf in
/-- The Lorentz invariants of the range of `f` reduce to the span of the image `f σ^^^` of the
  Pauli tensor. -/
noncomputable def invariantReductionToSpan :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  TensorSpecies.IsEquivariant.invariantReductionToSpan hf (complexLorentzTensor.isAdjointClosed _)
    σ^^^ toTensor_smul_eq_self exists_eq_smul_pauliMatrix_of_invariant

include hf in
/-- Every Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is a
  multiple of the image `f σ^^^` of the Pauli tensor plus an element of `S`, the shape of the
  fermion kinetic term. -/
lemma exists_smul_map_pauliMatrix_add_of_invariant (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ LinearMap.range f ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • f σ^^^ + y :=
  hf.invariantReductionToSpan.reduce S hS x hx hinv

end IsVectorLeftRightWeyl

/-!

## D. Dual Weyl indices

A family `T^μ{}_{α' α}` with a four-vector index and a dual right- and a dual left-handed Weyl
index is an equivariant map out of `ℂT[.up, .downR, .downL]`, `IsVectorDualLeftRightWeyl`.
Dualising both Weyl indices, `dualWeylMap`, is an equivariant surjection out of
`ℂT[.up, .upL, .upR]` which carries `σ^^^` to `σ^__`, so composing with it turns such a family
into an `IsVectorLeftRightWeyl` family with the same range, and section C applies.

-/

/-- A family with a four-vector index and a dual right- and a dual left-handed Weyl index
  `T^μ{}_{α' α}`, an equivariant linear map out of `ℂT[.up, .downR, .downL]`. -/
abbrev IsVectorDualLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.up, .downR, .downL] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz f

open PauliMatrix TensorSpecies Tensor in
/-- Dualising the two Weyl indices of a tensor with a four-vector index and a left-right Weyl
  pair, the dual indices listed in the order of `σ^__`. -/
noncomputable def dualWeylMap : ℂT[.up, .upL, .upR] →ₗ[ℂ] ℂT[.up, .downR, .downL] :=
  permT ![0, 2, 1] IsReindexing.auto ∘ₗ toDualMapAtIndex (S := complexLorentzTensor) 2 ∘ₗ
    toDualMapAtIndex (S := complexLorentzTensor) 1

open TensorSpecies Tensor in
/-- Dualising the Weyl indices commutes with the action of `SL(2,ℂ)`. -/
lemma dualWeylMap_equivariant (g : SL(2,ℂ)) (t : ℂT[.up, .upL, .upR]) :
    dualWeylMap (g • t) = g • dualWeylMap t := by
  rw [dualWeylMap, LinearMap.comp_apply, LinearMap.comp_apply, toDualMapAtIndex_equivariant,
    toDualMapAtIndex_equivariant, permT_equivariant]
  rfl

open PauliMatrix TensorSpecies Tensor in
/-- Dualising the Weyl indices of `σ^^^` gives `σ^__`. -/
lemma dualWeylMap_pauliMatrix : dualWeylMap σ^^^ = σ^__ := by
  rw [dualWeylMap, LinearMap.comp_apply, LinearMap.comp_apply,
    toTensor_dualWeyl_eq_pauliContrDown, permT_permT]
  exact permT_congr_eq_id _ _ _ (by decide)

open TensorSpecies Tensor in
/-- Dualising the Weyl indices is surjective. The dualisations are inverted by raising the
  indices again, and the relabelling by its inverse. -/
lemma dualWeylMap_surjective : Function.Surjective dualWeylMap := by
  intro t
  refine ⟨fromDualMapAtIndex (S := complexLorentzTensor) 1
    (fromDualMapAtIndex (S := complexLorentzTensor) 2 (permT ![0, 2, 1] IsReindexing.auto t)), ?_⟩
  rw [dualWeylMap, LinearMap.comp_apply, LinearMap.comp_apply,
    toDualMapAtIndex_fromDualMapAtIndex, toDualMapAtIndex_fromDualMapAtIndex, permT_permT]
  exact permT_congr_eq_id _ _ _ (by decide)

namespace IsVectorDualLeftRightWeyl

open PauliMatrix

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.up, .downR, .downL] →ₗ[ℂ] B}
  (hf : IsVectorDualLeftRightWeyl B repLorentz f)

include hf in
/-- Composing with the dualisation of the Weyl indices gives a family with a four-vector index
  and a left-right Weyl pair. -/
lemma isVectorLeftRightWeyl_comp_dualWeylMap :
    IsVectorLeftRightWeyl B repLorentz (f ∘ₗ dualWeylMap) where
  equivariant g t := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, dualWeylMap_equivariant, hf.equivariant]

/-- Composing with the dualisation of the Weyl indices does not change the range. -/
lemma range_comp_dualWeylMap : LinearMap.range (f ∘ₗ dualWeylMap) = LinearMap.range f :=
  LinearMap.range_comp_of_range_eq_top f (LinearMap.range_eq_top.2 dualWeylMap_surjective)

include hf in
/-- Every Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is a
  multiple of the image `f σ^__` of the Pauli tensor with dual Weyl indices plus an element of
  `S`, the kinetic term of a Weyl fermion. -/
lemma exists_smul_map_pauliContrDown_add_of_invariant (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ LinearMap.range f ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • f σ^__ + y := by
  have h := hf.isVectorLeftRightWeyl_comp_dualWeylMap.exists_smul_map_pauliMatrix_add_of_invariant
    S hS (by rwa [range_comp_dualWeylMap]) hinv
  rwa [LinearMap.comp_apply, dualWeylMap_pauliMatrix] at h

include hf in
/-- The Lorentz invariants of the range of `f` reduce to the span of the image `f σ^__` of the
  Pauli tensor with dual Weyl indices. -/
noncomputable def invariantReductionToSpan :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) where
  spanningVector := f σ^__
  stable := hf.isStableUnder_range
  spanningVector_fixed := hf.rep_map_of_invariant smul_pauliContrDown
  reduce S hS _ hx hinv := hf.exists_smul_map_pauliContrDown_add_of_invariant S hS hx hinv

end IsVectorDualLeftRightWeyl

/-!

## E. Maps from dual components

A family `T (μ, α, α')` of vectors, indexed by a four-vector index, a dual left-handed and a
dual right-handed Weyl index, is the linear map `ofDualVectorComponents T` sending
`e_μ ⊗ e_α' ⊗ e_α` to `T (μ, α, α')`, and it is equivariant when the vectors are moved as the
basis tensors are.

-/

section DualVectorComponents

open TensorSpecies Tensor

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

set_option backward.isDefEq.respectTransparency false in
/-- The component indices of a tensor of `ℂT[.up, .downR, .downL]`, as a four-vector index, a
  dual left-handed and a dual right-handed Weyl index. -/
def dualIndexEquiv : ComponentIdx (S := complexLorentzTensor) ![.up, .downR, .downL] ≃
    (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 where
  toFun v := (v 0, v 2, v 1)
  invFun v := fun | 0 => v.1 | 1 => v.2.2 | 2 => v.2.1
  left_inv v := by
    funext x
    fin_cases x <;> rfl
  right_inv v := rfl

/-- The linear map out of `ℂT[.up, .downR, .downL]` sending `e_μ ⊗ e_α' ⊗ e_α` to
  `T (μ, α, α')`. -/
noncomputable def ofDualVectorComponents (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) :
    ℂT[.up, .downR, .downL] →ₗ[ℂ] B :=
  (Tensor.basis _).constr ℂ fun φ => T (dualIndexEquiv φ)

/-- The range of `ofDualVectorComponents T` is the span of the vectors `T d`. -/
lemma range_ofDualVectorComponents (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) :
    LinearMap.range (ofDualVectorComponents T) = Submodule.span ℂ (Set.range T) := by
  rw [ofDualVectorComponents, Module.Basis.constr_range]
  exact congrArg _ (dualIndexEquiv.surjective.range_comp T)

/-- The image of `ofDualVectorComponents T` lies in the span of the vectors `T d`. -/
lemma ofDualVectorComponents_mem_span (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)
    (t : ℂT[.up, .downR, .downL]) :
    ofDualVectorComponents T t ∈ Submodule.span ℂ (Set.range T) := by
  rw [← range_ofDualVectorComponents]
  exact LinearMap.mem_range_self _ t

/-- `ofDualVectorComponents` of a sum of families is the sum of the maps. -/
lemma ofDualVectorComponents_sum {ι : Type*} (s : Finset ι)
    (T : ι → (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) :
    ofDualVectorComponents (fun d => ∑ i ∈ s, T i d) = ∑ i ∈ s, ofDualVectorComponents (T i) :=
  (Tensor.basis _).ext fun φ => by simp [ofDualVectorComponents, LinearMap.sum_apply]

/-- `ofDualVectorComponents T` is equivariant when `T (μ, α, α')` is moved as `T^μ{}_{α α'}`, the
  vector index by the Lorentz matrix, the dual left index by `(g⁻¹)ᵀ` and the dual right index
  by `(g⁻¹)ᴴ`, the summed index first in each factor. -/
lemma isVectorDualLeftRightWeyl_ofDualVectorComponents
    {repLorentz : Representation ℂ SL(2,ℂ) B} (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)
    (hT : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
      repLorentz g (T (μ, l)) = ∑ (ν : Fin 1 ⊕ Fin 3), ∑ (a : Fin 2 × Fin 2),
        ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
          * ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2)) • T (ν, a)) :
    IsVectorDualLeftRightWeyl B repLorentz (ofDualVectorComponents T) := by
  refine isEquivariant_constr _ fun g φ => ?_
  obtain ⟨⟨μ, l⟩, rfl⟩ := dualIndexEquiv.symm.surjective φ
  rw [Equiv.apply_symm_apply, hT, ← dualIndexEquiv.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Equiv.apply_symm_apply, Fin.prod_univ_three, mul_assoc]
  exact congrArg (· • _) (congrArg₂ (· * ·) (toMatrix_rep_up_apply g ν μ)
    ((congrArg₂ (· * ·) (congrFun (congrFun (toMatrix_rep_downR g) a.2) l.2)
      (congrFun (congrFun (toMatrix_rep_downL g) a.1) l.1)).trans (mul_comm _ _))).symm

open PauliMatrix in
/-- For a family whose map is equivariant, the Lorentz invariants of the span of the family
  reduce to the span of the image `ofDualVectorComponents T σ^__` of the Pauli tensor with dual
  Weyl indices. -/
noncomputable def IsVectorDualLeftRightWeyl.invariantReductionToComponentSpan
    {repLorentz : Representation ℂ SL(2,ℂ) B} {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}
    (hT : IsVectorDualLeftRightWeyl B repLorentz (ofDualVectorComponents T)) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g)
      (Submodule.span ℂ (Set.range T)) where
  spanningVector := ofDualVectorComponents T σ^__
  stable := range_ofDualVectorComponents T ▸ hT.isStableUnder_range
  spanningVector_fixed := hT.rep_map_of_invariant smul_pauliContrDown
  reduce S hS _ hx hinv := hT.exists_smul_map_pauliContrDown_add_of_invariant S hS
    (by rwa [range_ofDualVectorComponents]) hinv

end DualVectorComponents

/-!

## F. Once-derived one-index Weyl families and their products

A once-derived fermion symbol carries a four-vector index, from the derivative, besides its
spinor index. The derivative slot moves by the columns of the Lorentz matrix and the spinor
slot as in `IsDualLeftWeyl` or `IsDualRightWeyl`. A one-index family of one chirality times a
once-derived family of the other is a vector dual left-right Weyl family, in either order.

-/

section ChiralFamilies

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- A family `X` carrying one four-vector index and one dual undotted spinor index, the
  once-derived form of `IsDualLeftWeyl`, the derivative slot moving by the columns of the
  Lorentz matrix. Only the value index of a fermion symbol is dualised, so the derivative
  slot keeps the plain Lorentz law. -/
def IsVectorDualLeftWeyl (repLorentz : Representation ℂ SL(2,ℂ) B)
    (X : (Fin 1 ⊕ Fin 3) → Fin 2 → B) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : Fin 2), repLorentz Λ (X μ a)
    = ∑ ν, ∑ β, ((((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * (Λ⁻¹).1 a β) • X ν β

/-- A family `Y` carrying one four-vector index and one dual dotted spinor index, the
  once-derived form of `IsDualRightWeyl`. -/
def IsVectorDualRightWeyl (repLorentz : Representation ℂ SL(2,ℂ) B)
    (Y : (Fin 1 ⊕ Fin 3) → Fin 2 → B) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : Fin 2), repLorentz Λ (Y μ a)
    = ∑ ν, ∑ β, ((((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * star ((Λ⁻¹).1 a β)) • Y ν β

variable (hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
  repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)

include hrepLorentz_mul

/-- An undotted family times a once-derived dotted one is a vector dual left-right Weyl
  family, the derivative supplies the four-vector index. -/
lemma isVectorDualLeftRightWeyl_mul {X : Fin 2 → B} {Y : (Fin 1 ⊕ Fin 3) → Fin 2 → B}
    (hX : IsDualLeftWeyl repLorentz X) (hY : IsVectorDualRightWeyl repLorentz Y) :
    IsVectorDualLeftRightWeyl B repLorentz
      (ofDualVectorComponents fun p => X p.2.1 * Y p.1 p.2.2) :=
  isVectorDualLeftRightWeyl_ofDualVectorComponents _ fun g μ l => by
    rw [hrepLorentz_mul, hX g l.1, hY g μ l.2, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, ← SL2C.inverse_coe]
    ring

/-- A dotted family times a once-derived undotted one is a vector dual left-right Weyl
  family, the two spinor slots exchanged. -/
lemma isVectorDualLeftRightWeyl_mul_swap {X : Fin 2 → B} {Y : (Fin 1 ⊕ Fin 3) → Fin 2 → B}
    (hX : IsDualRightWeyl repLorentz X) (hY : IsVectorDualLeftWeyl repLorentz Y) :
    IsVectorDualLeftRightWeyl B repLorentz
      (ofDualVectorComponents fun p => X p.2.2 * Y p.1 p.2.1) :=
  isVectorDualLeftRightWeyl_ofDualVectorComponents _ fun g μ l => by
    rw [hrepLorentz_mul, hX g l.2, hY g μ l.1, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, ← SL2C.inverse_coe]
    ring

end ChiralFamilies

end Lorentz
