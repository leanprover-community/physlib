/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Bispinors.Pauli.Basic
public import PhyslibAlpha.Relativity.SL2C.Basic
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre
public import PhyslibAlpha.Relativity.Fermions.Weyl.Metric
public import PhyslibAlpha.Relativity.PauliMatrices.ToTensor
/-!
# The Pauli tensor is the unique invariant

Up to scale, the Pauli tensor `σ^{μ α α̇}` is the only invariant with a vector, a left-handed and a
right-handed Weyl index.

## i. Overview

The covariant Pauli matrices `σ_μ = η_{μμ} σ^μ` move under `M ∈ SL(2, ℂ)` as a covariant vector,
`M σ_μ Mᴴ = Σ_ν Λ_{ν μ} σ_ν`, so `e_μ ↦ σ_μ` is an equivariant linear map `contrToLeftRight`
from the complex four-vectors to `LeftHandedWeyl ⊗ RightHandedWeyl` (A). By the Fierz completeness
relation the `σ_μ` span all `2 × 2` matrices, so this map is onto. Applied to the second index of
the metric `η^{μν}` it gives the Pauli tensor `pauliVal`, the two lowerings cancelling (B).

The map `contrToLeftRight` is onto between spaces of dimension four, so it is bijective, and so
is `id ⊗ contrToLeftRight`. It carries the invariants of `ComplexVector ⊗ ComplexVector`, the line
through the metric, onto those of `ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)`, which are
therefore the line through `σ` (C). Section D restates this for the complex Lorentz tensors
`ℂT[.up, .upL, .upR]` and their dual-Weyl form `ℂT[.up, .downR, .downL]`, and applies it to
equivariant maps out of them, the shape of the fermion kinetic term.

## ii. Key results

- `Lorentz.ComplexVector.contrToLeftRight` : the equivariant map `e_μ ↦ σ_μ`.
- `Lorentz.ComplexVector.lTensor_contrToLeftRight_metricVal` : it carries the metric to the Pauli
  tensor.
- `Lorentz.ComplexVector.invariants_tprod_eq_span_pauliVal` : the invariants are the line through
  the Pauli tensor.
- `Lorentz.invariants_tensorRep_eq_span_pauliMatrix` : the invariant tensors of
  `ℂT[.up, .upL, .upR]` are the line through `σ^^^`.
- `Lorentz.invariantReductionToPauliMatrix`, `Lorentz.invariantReductionToPauliContrDown` : the
  invariants of the range of an equivariant map reduce to the image of the Pauli tensor.
- `Lorentz.isEquivariant_upDownRDownL_mul` : a one-index family times a once-derived one of the
  other chirality is an equivariant map out of `ℂT[.up, .downR, .downL]`.

## iii. Table of contents

- A. The Pauli matrices as an equivariant map
- B. The metric goes to the Pauli tensor
- C. The Pauli tensor is the unique invariant
- D. The Pauli tensor with three indices
  - D.1. The invariant tensors
  - D.2. The classification of the Lorentz invariants
  - D.3. Dual Weyl indices
  - D.4. Maps from dual components
  - D.5. Once-derived one-index Weyl families and their products

## iv. References

The Pauli tensor `ComplexVector.pauliVal` and the intertwining map `ComplexVector.pauli` are in
`Physlib.Relativity.Bispinors.Pauli.Basic`, where sections A to C are written to move. The
uniqueness of the metric of the complex four-vectors is in
`PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre`.

-/

@[expose] public section

namespace Lorentz.ComplexVector

open Matrix MatrixGroups TensorProduct Fermion PauliMatrix

noncomputable section

/-!

## A. The Pauli matrices as an equivariant map

-/

/-- The covariant Pauli matrices as a map `e_μ ↦ σ_μ` from complex four-vectors to a left- and a
  right-handed Weyl index. -/
def contrToLeftRightLinear : ComplexVector →ₗ[ℂ] LeftHandedWeyl ⊗[ℂ] RightHandedWeyl :=
  ComplexVector.basis.constr ℂ fun μ => leftRightToMatrix.symm (pauliLower μ)

/-- The basis vector `e_μ` is sent to the lowered Pauli matrix `σ_μ`. -/
lemma contrToLeftRightLinear_basis (μ : Fin 1 ⊕ Fin 3) :
    contrToLeftRightLinear (ComplexVector.basis μ) = leftRightToMatrix.symm (pauliLower μ) :=
  ComplexVector.basis.constr_basis ℂ _ μ

/-- The covariant Pauli matrices move as a covariant vector, so `e_μ ↦ σ_μ` is equivariant. -/
lemma contrToLeftRightLinear_rep (M : SL(2,ℂ)) (v : ComplexVector) :
    contrToLeftRightLinear (ComplexVector.SL2CRep M v) =
      TensorProduct.map (LeftHandedWeyl.rep M) (RightHandedWeyl.rep M)
        (contrToLeftRightLinear v) := by
  have h : contrToLeftRightLinear ∘ₗ ComplexVector.SL2CRep M =
      TensorProduct.map (LeftHandedWeyl.rep M) (RightHandedWeyl.rep M) ∘ₗ
        contrToLeftRightLinear := by
    refine ComplexVector.basis.ext fun μ => ?_
    simp only [LinearMap.comp_apply]
    rw [SL2CRep_ρ_basis, contrToLeftRightLinear_basis, ← pauliBasis'_coe,
      leftRightToMatrix_ρ_symm_selfAdjoint _ (pauliBasis' μ).2]
    change _ = leftRightToMatrix.symm (SL2C.toSelfAdjointMap M (pauliBasis' μ)).1
    have hs (r : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
        leftRightToMatrix.symm (r • X) = r • leftRightToMatrix.symm X :=
      leftRightToMatrix.symm.toLinearMap.map_smul_of_tower r X
    rw [SL2C.toSelfAdjointMap_basis]
    simp [map_sum, LinearMap.map_smul_of_tower, contrToLeftRightLinear_basis, pauliBasis'_coe,
      selfAdjoint.val_smul, hs]
  exact LinearMap.congr_fun h v

/-- The covariant Pauli matrices as an intertwining map `e_μ ↦ σ_μ` from complex four-vectors to
  a left- and a right-handed Weyl index. -/
def contrToLeftRight :
    ComplexVector.SL2CRep.IntertwiningMap (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep) :=
  contrToLeftRightLinear.intertwiningMap_of_isIntertwiningMap _ _ contrToLeftRightLinear_rep

/-- The basis vector `e_μ` is sent to the lowered Pauli matrix `σ_μ`. -/
lemma contrToLeftRight_basis (μ : Fin 1 ⊕ Fin 3) :
    contrToLeftRight (ComplexVector.basis μ) = leftRightToMatrix.symm (pauliLower μ) :=
  contrToLeftRightLinear_basis μ

/-- The covariant Pauli matrices span the `2 × 2` matrices, by the Fierz completeness relation,
  so `e_μ ↦ σ_μ` is onto. -/
lemma contrToLeftRight_surjective : Function.Surjective contrToLeftRight := by
  intro t
  obtain ⟨(X : Matrix (Fin 2) (Fin 2) ℂ), rfl⟩ := leftRightToMatrix.symm.surjective t
  refine ⟨∑ ρ, ((2 : ℂ)⁻¹ * ∑ β : Fin 2, ∑ β' : Fin 2, X β β' * pauliLower ρ β' β) •
    ComplexVector.basis ρ, ?_⟩
  apply leftRightToMatrix.symm.symm.injective
  simp only [map_sum, map_smul, contrToLeftRight_basis, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply]
  refine Matrix.ext fun α α' => ?_
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ ρ, (2⁻¹ * ∑ β : Fin 2, ∑ β' : Fin 2, X β β' * pauliLower ρ β' β) * pauliLower ρ α α'
      = 2⁻¹ * ∑ β : Fin 2, ∑ β' : Fin 2, X β β' *
          ∑ ρ, pauliLower ρ β' β * pauliLower ρ α α' := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β' _ => Finset.sum_congr rfl fun ρ _ => by ring
    _ = X α α' := by
        simp only [sum_pauliLower_mul_pauliLower, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
        ring

/-!

## B. The metric goes to the Pauli tensor

-/

/-- Applying `e_μ ↦ σ_μ` to the second index of the metric `η^{μν}` gives the Pauli tensor. The
  lowering in `σ_μ` cancels the metric. -/
lemma lTensor_contrToLeftRight_metricVal :
    contrToLeftRight.lTensor ComplexVector.SL2CRep ComplexVector.metricVal =
      ComplexVector.pauliVal := by
  rw [ComplexVector.metricVal_expand_tmul, ComplexVector.pauliVal_expand_basis]
  simp only [map_sub, Representation.IntertwiningMap.lTensor_apply, contrToLeftRight_basis,
    pauliLower_eq_smul]
  simp [minkowskiMatrixZ, pauliBasis, pauliSelfAdjoint, sub_eq_add_neg, tmul_neg]

/-!

## C. The Pauli tensor is the unique invariant

-/

/-- The map `e_μ ↦ σ_μ` is bijective: it is onto, between spaces of dimension four. -/
lemma contrToLeftRight_bijective : Function.Bijective contrToLeftRight := by
  have := Module.Finite.of_basis ComplexVector.basis
  have := Module.Finite.of_basis LeftHandedWeyl.basis
  have := Module.Finite.of_basis RightHandedWeyl.basis
  have h : Module.finrank ℂ ComplexVector =
      Module.finrank ℂ (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl) := by
    rw [Module.finrank_tensorProduct, Module.finrank_eq_card_basis ComplexVector.basis,
      Module.finrank_eq_card_basis LeftHandedWeyl.basis,
      Module.finrank_eq_card_basis RightHandedWeyl.basis]
    simp
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank h
    (f := contrToLeftRight.toLinearMap)).2 contrToLeftRight_surjective,
    contrToLeftRight_surjective⟩

/-- The `SL(2,ℂ)`-invariants of `ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)` are the line
  through the Pauli tensor `σ^{μ α α̇}`. The bijection `id ⊗ contrToLeftRight` carries the
  invariants of `ComplexVector ⊗ ComplexVector`, the line through the metric, onto them. -/
lemma invariants_tprod_eq_span_pauliVal :
    (ComplexVector.SL2CRep.tprod (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep)).invariants =
      ℂ ∙ ComplexVector.pauliVal := by
  let e := LinearEquiv.ofBijective contrToLeftRight.toLinearMap contrToLeftRight_bijective
  have hbij : Function.Bijective (contrToLeftRight.lTensor ComplexVector.SL2CRep) :=
    (LinearEquiv.lTensor ComplexVector e).bijective
  rw [Representation.invariants_eq_map_of_bijective _ hbij,
    ComplexVector.invariants_tprod_eq_span_metricVal, Submodule.map_span, Set.image_singleton,
    Representation.IntertwiningMap.toLinearMap_apply, lTensor_contrToLeftRight_metricVal]

end

end Lorentz.ComplexVector

/-!

## D. The Pauli tensor with three indices

The invariant tensors of `ℂT[.up, .upL, .upR]` are the line through `σ^^^`, the Pauli matrices as
a tensor (D.1). Such a tensor is `fromTripleT` of an element of
`ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)`, whose invariants are the line through
`pauliVal`. So for an equivariant map `f` out of `ℂT[.up, .upL, .upR]` every Lorentz invariant in
the range of `f` is a multiple of `f σ^^^`, modulo a Lorentz-stable submodule, the shape of the
fermion kinetic term `ψ̄_{α'} σ̄^{μ α' α} ∂_μ ψ_α`, `invariantReductionToPauliMatrix` (D.2).

The Standard Model's fermion symbols are `Module.Dual`-valued, so their spinor indices are dual
Weyl indices, and a family of them is an equivariant map out of `ℂT[.up, .downR, .downL]`.
Dualising both Weyl indices, `dualWeylMap`, is an equivariant surjection from
`ℂT[.up, .upL, .upR]` carrying `σ^^^` to `σ^__`, so every invariant in the range of such a map is
a multiple of `f σ^__` (D.3). A family indexed by a four-vector, a dual left-handed and a dual
right-handed Weyl index is relabelled by `dualIndexEquiv`, and its map is equivariant when it
obeys the transformation law of these indices (D.4). A one-index Weyl family times a once-derived
one of the other chirality is such a family, the shape of the fermion kinetic term (D.5).

-/

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C TensorSpecies complexLorentzTensor


/-!

### D.1. The invariant tensors

A tensor of `ℂT[.up, .upL, .upR]` is `fromTripleT` of an element of
`ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)`, whose invariants are the line through the
Pauli tensor `ComplexVector.pauliVal`, and `fromTripleT` of that is `σ^^^`.

-/

open PauliMatrix in
/-- The invariant tensors with a four-vector index and a left-right Weyl pair are the line
  through the Pauli tensor. -/
lemma invariants_tensorRep_eq_span_pauliMatrix :
    (complexLorentzTensor.tensorRep ![.up, .upL, .upR]).invariants = ℂ ∙ σ^^^ := by
  rw [TensorSpecies.invariants_tensorRep_triple_eq_span (S := complexLorentzTensor) (c1 := .up)
    (c2 := .upL) (c3 := .upR) ComplexVector.invariants_tprod_eq_span_pauliVal, toTensor_eq_pauli,
    TensorSpecies.Tensor.fromConstTriple, ComplexVector.pauli_apply_one]

/-!

### D.2. The classification of the Lorentz invariants

-/

/-- For an equivariant map `f` out of `ℂT[.up, .upL, .upR]`, the Lorentz invariants of the range
  of `f` reduce to the span of the image `f σ^^^` of the Pauli tensor. -/
noncomputable def invariantReductionToPauliMatrix {B : Type*} [AddCommGroup B] [Module ℂ B]
    {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B}
    (hf : complexLorentzTensor.IsEquivariant ![.up, .upL, .upR] repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  hf.invariantReductionToSpan (complexLorentzTensor.hasReynolds _)
    invariants_tensorRep_eq_span_pauliMatrix

/-!

### D.3. Dual Weyl indices

A family `T^μ{}_{α' α}` with a four-vector index and a dual right- and a dual left-handed Weyl
index is an equivariant map out of `ℂT[.up, .downR, .downL]`. Dualising both Weyl indices,
`dualWeylMap`, is an equivariant surjection out of `ℂT[.up, .upL, .upR]` which carries `σ^^^` to
`σ^__`, so composing with it gives an equivariant map out of `ℂT[.up, .upL, .upR]` with the same
range, and section D.2 applies.

-/

open PauliMatrix TensorSpecies TensorSpecies.Tensor in
/-- Dualising the two Weyl indices of a tensor with a four-vector index and a left-right Weyl
  pair, the dual indices listed in the order of `σ^__`. -/
noncomputable def dualWeylMap : ℂT[.up, .upL, .upR] →ₗ[ℂ] ℂT[.up, .downR, .downL] :=
  permT ![0, 2, 1] IsReindexing.auto ∘ₗ toDualMapAtIndex (S := complexLorentzTensor) 2 ∘ₗ
    toDualMapAtIndex (S := complexLorentzTensor) 1

open TensorSpecies TensorSpecies.Tensor in
/-- Dualising the Weyl indices commutes with the action of `SL(2,ℂ)`. -/
lemma dualWeylMap_equivariant (g : SL(2,ℂ)) (t : ℂT[.up, .upL, .upR]) :
    dualWeylMap (g • t) = g • dualWeylMap t := by
  rw [dualWeylMap, LinearMap.comp_apply, LinearMap.comp_apply, toDualMapAtIndex_equivariant,
    toDualMapAtIndex_equivariant, permT_equivariant]
  rfl

open PauliMatrix TensorSpecies TensorSpecies.Tensor in
/-- Dualising the Weyl indices of `σ^^^` gives `σ^__`. -/
lemma dualWeylMap_pauliMatrix : dualWeylMap σ^^^ = σ^__ := by
  rw [dualWeylMap, LinearMap.comp_apply, LinearMap.comp_apply,
    toTensor_dualWeyl_eq_pauliContrDown, permT_permT]
  exact permT_congr_eq_id _ _ _ (by decide)

open TensorSpecies TensorSpecies.Tensor in
/-- Dualising the Weyl indices is surjective. The dualisations are inverted by raising the
  indices again, and the relabelling by its inverse. -/
lemma dualWeylMap_surjective : Function.Surjective dualWeylMap := by
  intro t
  refine ⟨fromDualMapAtIndex (S := complexLorentzTensor) 1
    (fromDualMapAtIndex (S := complexLorentzTensor) 2 (permT ![0, 2, 1] IsReindexing.auto t)), ?_⟩
  rw [dualWeylMap, LinearMap.comp_apply, LinearMap.comp_apply,
    toDualMapAtIndex_fromDualMapAtIndex, toDualMapAtIndex_fromDualMapAtIndex, permT_permT]
  exact permT_congr_eq_id _ _ _ (by decide)

section DualWeyl

open PauliMatrix

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.up, .downR, .downL] →ₗ[ℂ] B}
  (hf : complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz f)

include hf in
/-- Composing with the dualisation of the Weyl indices gives an equivariant map out of
  `ℂT[.up, .upL, .upR]`. -/
lemma isEquivariant_comp_dualWeylMap :
    complexLorentzTensor.IsEquivariant ![.up, .upL, .upR] repLorentz (f ∘ₗ dualWeylMap) where
  equivariant g t := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, dualWeylMap_equivariant, hf.equivariant]

/-- Composing with the dualisation of the Weyl indices does not change the range. -/
lemma range_comp_dualWeylMap : LinearMap.range (f ∘ₗ dualWeylMap) = LinearMap.range f :=
  LinearMap.range_comp_of_range_eq_top f (LinearMap.range_eq_top.2 dualWeylMap_surjective)

include hf in
/-- The Lorentz invariants of the range of `f` reduce to the span of the image `f σ^__` of the
  Pauli tensor with dual Weyl indices, the kinetic term of a Weyl fermion. -/
noncomputable def invariantReductionToPauliContrDown :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  (isEquivariant_comp_dualWeylMap hf).invariantReductionToSpanOfEq
    (complexLorentzTensor.hasReynolds _) invariants_tensorRep_eq_span_pauliMatrix
    range_comp_dualWeylMap (f σ^__) (by rw [LinearMap.comp_apply, dualWeylMap_pauliMatrix])

end DualWeyl

/-!

### D.4. Maps from dual components

A family `T (μ, α, α')` of vectors, indexed by a four-vector index, a dual left-handed and a
dual right-handed Weyl index, is relabelled by `dualIndexEquiv`, and its map
`ofComponents (T ∘ dualIndexEquiv)` sends `e_μ ⊗ e_α' ⊗ e_α` to `T (μ, α, α')`. It is equivariant
when the vectors are moved as the basis tensors are.

-/

section DualVectorComponents

open TensorSpecies.Tensor hiding ofComponents

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

/-- The map of a family relabelled by `dualIndexEquiv` is equivariant when `T (μ, α, α')` is moved
  as `T^μ{}_{α α'}`, the vector index by the Lorentz matrix, the dual left index by `(g⁻¹)ᵀ` and
  the dual right index by `(g⁻¹)ᴴ`, the summed index first in each factor. -/
lemma isEquivariant_ofComponents_upDownRDownL
    {repLorentz : Representation ℂ SL(2,ℂ) B} (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)
    (hT : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
      repLorentz g (T (μ, l)) = ∑ (ν : Fin 1 ⊕ Fin 3), ∑ (a : Fin 2 × Fin 2),
        ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
          * ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2)) • T (ν, a)) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (ofComponents (T ∘ dualIndexEquiv)) := by
  refine (isEquivariant_ofComponents_iff _).2 fun g φ => ?_
  obtain ⟨⟨μ, l⟩, rfl⟩ := dualIndexEquiv.symm.surjective φ
  rw [Function.comp_apply, Equiv.apply_symm_apply, hT, ← dualIndexEquiv.symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Function.comp_apply, Equiv.apply_symm_apply, Fin.prod_univ_three, mul_assoc]
  exact congrArg (· • _) (congrArg₂ (· * ·) (toMatrix_rep_up_apply g ν μ)
    ((congrArg₂ (· * ·) (congrFun (congrFun (toMatrix_rep_downR g) a.2) l.2)
      (congrFun (congrFun (toMatrix_rep_downL g) a.1) l.1)).trans (mul_comm _ _))).symm

open PauliMatrix in
/-- For a family whose map is equivariant, the Lorentz invariants of the span of the family
  reduce to the span of the image `ofComponents (T ∘ dualIndexEquiv) σ^__` of the Pauli tensor
  with dual Weyl indices. -/
noncomputable def invariantReductionToPauliContrDownOfComponents
    {repLorentz : Representation ℂ SL(2,ℂ) B} {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}
    (hT : complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (ofComponents (T ∘ dualIndexEquiv))) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g)
      (Submodule.span ℂ (Set.range T)) :=
  (isEquivariant_comp_dualWeylMap hT).invariantReductionToSpanOfEq
    (complexLorentzTensor.hasReynolds _) invariants_tensorRep_eq_span_pauliMatrix
    (range_comp_dualWeylMap.trans (range_ofComponents_comp dualIndexEquiv T))
    (ofComponents (T ∘ dualIndexEquiv) σ^__) (by rw [LinearMap.comp_apply, dualWeylMap_pauliMatrix])

end DualVectorComponents

/-!

### D.5. Once-derived one-index Weyl families and their products

A once-derived fermion symbol carries a four-vector index, from the derivative, besides its
spinor index. The derivative slot moves by the columns of the Lorentz matrix and the spinor
slot by the contragredient of the Weyl representation of its chirality, conjugated for the
dotted one. Only the value index of a fermion symbol is dualised, so the derivative slot keeps the
plain Lorentz law. A one-index family of one chirality times a once-derived family of the other
is an equivariant map out of `ℂT[.up, .downR, .downL]`, in either order.

-/

section ChiralFamilies

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}
  (hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)

include hrepLorentz_mul

/-- An undotted family times a once-derived dotted one is an equivariant map out of
  `ℂT[.up, .downR, .downL]`, the derivative supplying the four-vector index. -/
lemma isEquivariant_upDownRDownL_mul {X : Fin 2 → B} {Y : (Fin 1 ⊕ Fin 3) → Fin 2 → B}
    (hX : ∀ (Λ : SL(2,ℂ)) (a : Fin 2), repLorentz Λ (X a) = ∑ β, (Λ⁻¹).1 a β • X β)
    (hY : ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : Fin 2), repLorentz Λ (Y μ a)
      = ∑ ν, ∑ β, ((((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * star ((Λ⁻¹).1 a β)) • Y ν β) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (ofComponents ((fun p => X p.2.1 * Y p.1 p.2.2) ∘ dualIndexEquiv)) :=
  isEquivariant_ofComponents_upDownRDownL _ fun g μ l => by
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

/-- A dotted family times a once-derived undotted one is an equivariant map out of
  `ℂT[.up, .downR, .downL]`, the two spinor slots exchanged. -/
lemma isEquivariant_upDownRDownL_mul_swap {X : Fin 2 → B} {Y : (Fin 1 ⊕ Fin 3) → Fin 2 → B}
    (hX : ∀ (Λ : SL(2,ℂ)) (a : Fin 2), repLorentz Λ (X a) = ∑ β, star ((Λ⁻¹).1 a β) • X β)
    (hY : ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : Fin 2), repLorentz Λ (Y μ a)
      = ∑ ν, ∑ β, ((((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * (Λ⁻¹).1 a β) • Y ν β) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (ofComponents ((fun p => X p.2.2 * Y p.1 p.2.1) ∘ dualIndexEquiv)) :=
  isEquivariant_ofComponents_upDownRDownL _ fun g μ l => by
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
