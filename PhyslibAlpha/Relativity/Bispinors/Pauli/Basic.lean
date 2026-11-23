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
public import PhyslibAlpha.Relativity.Fermions.Weyl.Tensorial
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.Tensorial
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
therefore the line through `σ` (C). The tensor product is tensorial, so section D restates this
for the tensor `toTensor pauliVal`, relabelled as the tensor `pauliTensor` of
`ℂT[.up, .upL, .upR]`, the line through which is the invariant tensors with a four-vector and a
left-right Weyl pair of indices, and for its dual-Weyl form in `ℂT[.up, .downR, .downL]`. It then
applies this to equivariant maps out of these tensors, the shape of the fermion kinetic term.

## ii. Key results

- `Lorentz.ComplexVector.contrToLeftRight` : the equivariant map `e_μ ↦ σ_μ`.
- `Lorentz.ComplexVector.lTensor_contrToLeftRight_metricVal` : it carries the metric to the Pauli
  tensor.
- `Lorentz.ComplexVector.invariants_tprod_eq_span_pauliVal` : the invariants are the line through
  the Pauli tensor.
- `Lorentz.pauliTensor` : the Pauli tensor as a tensor of `ℂT[.up, .upL, .upR]`.
- `complexLorentzTensor.invariants_up_upL_upR_eq_span_pauli` : the invariant tensors with the
  indices of the Pauli tensor are the line through `pauliTensor`.
- `Lorentz.invariantReductionToPauliVal`, `Lorentz.invariantReductionToPauliValDualWeyl` : the
  invariants of the range of an equivariant map reduce to the image of the Pauli tensor.
- `Lorentz.isEquivariant_upDownRDownL_mul` : a one-index family times a once-derived one of the
  other chirality is an equivariant map out of `ℂT[.up, .downR, .downL]`.

## iii. Table of contents

- A. The Pauli matrices as an equivariant map
- B. The metric goes to the Pauli tensor
- C. The Pauli tensor is the unique invariant
- D. The Pauli tensor as a complex Lorentz tensor
  - D.1. The invariant tensors
  - D.2. Dual Weyl indices
  - D.3. Maps from dual components
  - D.4. Once-derived one-index Weyl families and their products

## iv. References

The Pauli tensor `ComplexVector.pauliVal` and the intertwining map `ComplexVector.pauli` are in
`Physlib.Relativity.Bispinors.Pauli.Basic`, where sections A to C are written to move. The
uniqueness of the metric of the complex four-vectors is in
`PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre`. The tensorial structures of the
three factors are in `PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.Tensorial` and
`PhyslibAlpha.Relativity.Fermions.Weyl.Tensorial`.

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

## D. The Pauli tensor as a complex Lorentz tensor

Complex four-vectors and Weyl fermions are tensorial, so
`ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)` is tensorial through
`TensorSpecies.Tensorial.prod`. Its tensors carry the indices
`Fin.append ![.up] (Fin.append ![.upL] ![.upR])`, and the Pauli tensor is the tensor
`toTensor pauliVal`. The equivalence `toTensor` carries the action of `SL(2, ℂ)` on the tensor
product to the action on tensors, so the invariant tensors are the line through
`toTensor pauliVal`. Relabelling the colours as the plain list `![.up, .upL, .upR]`
(`isReindexing_append_three`), the invariant tensors of `ℂT[.up, .upL, .upR]` are the line
through the relabelled tensor `pauliTensor`. For an equivariant map `f` out of these tensors every
Lorentz invariant in the range of `f` is then a multiple of `f pauliTensor`, modulo a
Lorentz-stable submodule, `invariantReductionToPauliVal` (D.1).

The Standard Model's fermion symbols are `Module.Dual`-valued, so their spinor indices are dual
Weyl indices, and a family of them is an equivariant map out of `ℂT[.up, .downR, .downL]`.
Dualising both Weyl indices, `dualWeylMap`, is an equivariant surjection onto these tensors, so
every invariant in the range of such a map `f` is a multiple of
`f (dualWeylMap pauliTensor)`, the image of the Pauli tensor with dual Weyl indices (D.2).
A family indexed by a four-vector, a dual left-handed and a dual right-handed Weyl index is
relabelled by `dualIndexEquiv`, and its map is equivariant when it obeys the transformation law
of these indices (D.3). A one-index Weyl family times a once-derived one of the other chirality
is such a family, the shape of the fermion kinetic term (D.4).

-/

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C TensorSpecies TensorSpecies.Tensorial
  complexLorentzTensor Fermion

/-!

### D.1. The invariant tensors

-/

/-- The equivalence `toTensor` carries the action of `SL(2, ℂ)` on
  `ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)` to the action on tensors. -/
lemma ComplexVector.toTensor_SL2CRep_tprod (g : SL(2,ℂ))
    (x : ComplexVector ⊗[ℂ] (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl)) :
    toTensor ((ComplexVector.SL2CRep.tprod (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep)) g x)
      = g • toTensor x := by
  induction x using TensorProduct.inductionOn with
  | tmul v y =>
    induction y using TensorProduct.inductionOn with
    | tmul l r =>
      simp only [Representation.tprod_apply, TensorProduct.map_tmul, toTensor_tprod]
      rw [ComplexVector.toTensor_SL2CRep, LeftHandedWeyl.toTensor_rep,
        RightHandedWeyl.toTensor_rep, Tensor.prodT_equivariant, Tensor.prodT_equivariant]
    | add y y' hy hy' => simp_all [TensorProduct.tmul_add]
  | add x x' hx hx' => simp_all

/-- The Pauli tensor `σ^{μ α α̇}` as a tensor of `ℂT[.up, .upL, .upR]`, the tensor
  `toTensor pauliVal` with its colours `Fin.append ![.up] (Fin.append ![.upL] ![.upR])` relabelled
  as the plain list. -/
noncomputable def pauliTensor : ℂT[.up, .upL, .upR] :=
  Tensor.permT id (isReindexing_append_three _ _ _) (toTensor ComplexVector.pauliVal)

/-- The invariant tensors with a four-vector index and a left-right Weyl pair are the line
  through the Pauli tensor. The equivalence `toTensor` carries the invariants of the tensor
  product, the line through `pauliVal`, onto the invariant tensors of the colours of the
  tensorial structure, and relabelling the colours carries these onto those of the plain list. -/
lemma _root_.complexLorentzTensor.invariants_up_upL_upR_eq_span_pauli :
    (complexLorentzTensor.tensorRep ![.up, .upL, .upR]).invariants = ℂ ∙ pauliTensor := by
  have h : (complexLorentzTensor.tensorRep
      (Fin.append ![.up] (Fin.append ![.upL] ![.upR]))).invariants =
      ℂ ∙ toTensor ComplexVector.pauliVal := by
    rw [invariants_tensorRep_eq_map_of_equiv toTensor ComplexVector.toTensor_SL2CRep_tprod,
      ComplexVector.invariants_tprod_eq_span_pauliVal, Submodule.map_span, Set.image_singleton]
    rfl
  rw [invariants_tensorRep_eq_span_of_permT (isReindexing_append_three _ _ _) h,
    Set.image_singleton]
  rfl

/-- For an equivariant map `f` out of the tensors with the indices of the Pauli tensor, the
  Lorentz invariants of the range of `f` reduce to the span of the image `f pauliTensor` of the
  Pauli tensor. -/
noncomputable def invariantReductionToPauliVal {B : Type*} [AddCommGroup B] [Module ℂ B]
    {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B}
    (hf : complexLorentzTensor.IsEquivariant ![.up, .upL, .upR] repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  hf.invariantReductionToSpan (complexLorentzTensor.hasReynolds _)
    invariants_up_upL_upR_eq_span_pauli

/-!

### D.2. Dual Weyl indices

A family `T^μ{}_{α' α}` with a four-vector index and a dual right- and a dual left-handed Weyl
index is an equivariant map out of `ℂT[.up, .downR, .downL]`. Dualising both Weyl indices,
`dualWeylMap`, is an equivariant surjection onto these tensors from the tensors with the indices
of the Pauli tensor. Composing with it gives an equivariant map with the same range out of the
latter, and section D.1 applies.

-/

open TensorSpecies.Tensor in
/-- Dualising the two Weyl indices of a tensor with the indices of the Pauli tensor, the dual
  indices listed in the order of `ℂT[.up, .downR, .downL]`. -/
noncomputable def dualWeylMap : ℂT[.up, .upL, .upR] →ₗ[ℂ] ℂT[.up, .downR, .downL] :=
  permT ![0, 2, 1] IsReindexing.auto ∘ₗ toDualMapAtIndex (S := complexLorentzTensor) 2 ∘ₗ
    toDualMapAtIndex (S := complexLorentzTensor) 1

open TensorSpecies.Tensor in
/-- Dualising the Weyl indices commutes with the action of `SL(2,ℂ)`. -/
lemma dualWeylMap_equivariant (g : SL(2,ℂ)) (t : ℂT[.up, .upL, .upR]) :
    dualWeylMap (g • t) = g • dualWeylMap t := by
  rw [dualWeylMap, LinearMap.comp_apply, LinearMap.comp_apply, toDualMapAtIndex_equivariant,
    toDualMapAtIndex_equivariant, permT_equivariant]
  rfl

open TensorSpecies.Tensor in
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

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.up, .downR, .downL] →ₗ[ℂ] B}
  (hf : complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz f)

include hf in
/-- Composing with the dualisation of the Weyl indices gives an equivariant map out of the
  tensors with the indices of the Pauli tensor. -/
lemma isEquivariant_comp_dualWeylMap :
    complexLorentzTensor.IsEquivariant ![.up, .upL, .upR] repLorentz (f ∘ₗ dualWeylMap) where
  equivariant g t := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, dualWeylMap_equivariant, hf.equivariant]

/-- Composing with the dualisation of the Weyl indices does not change the range. -/
lemma range_comp_dualWeylMap : LinearMap.range (f ∘ₗ dualWeylMap) = LinearMap.range f :=
  LinearMap.range_comp_of_range_eq_top f (LinearMap.range_eq_top.2 dualWeylMap_surjective)

include hf in
/-- The Lorentz invariants of the range of `f` reduce to the span of the image
  `f (dualWeylMap pauliTensor)` of the Pauli tensor with dual Weyl indices, the kinetic term of a
  Weyl fermion. -/
noncomputable def invariantReductionToPauliValDualWeyl :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  (isEquivariant_comp_dualWeylMap hf).invariantReductionToSpanOfEq
    (complexLorentzTensor.hasReynolds _) invariants_up_upL_upR_eq_span_pauli
    range_comp_dualWeylMap (f (dualWeylMap pauliTensor)) rfl

end DualWeyl

/-!

### D.3. Maps from dual components

A family `T (μ, α, α')` of vectors, indexed by a four-vector index, a dual left-handed and a
dual right-handed Weyl index, is relabelled by `dualIndexEquiv`, and its map
`liftComponents (T ∘ dualIndexEquiv)` sends `e_μ ⊗ e_α' ⊗ e_α` to `T (μ, α, α')`. It is
equivariant when the vectors are moved as the basis tensors are.

-/

section DualVectorComponents

open TensorSpecies.Tensor

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
lemma isEquivariant_liftComponents_upDownRDownL
    {repLorentz : Representation ℂ SL(2,ℂ) B} (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)
    (hT : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
      repLorentz g (T (μ, l)) = ∑ (ν : Fin 1 ⊕ Fin 3), ∑ (a : Fin 2 × Fin 2),
        ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
          * ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2)) • T (ν, a)) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents (T ∘ dualIndexEquiv)) := by
  refine (isEquivariant_liftComponents_iff _).2 fun g φ => ?_
  obtain ⟨⟨μ, l⟩, rfl⟩ := dualIndexEquiv.symm.surjective φ
  rw [Function.comp_apply, Equiv.apply_symm_apply, hT, ← dualIndexEquiv.symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Function.comp_apply, Equiv.apply_symm_apply, Fin.prod_univ_three, mul_assoc]
  exact congrArg (· • _) (congrArg₂ (· * ·) (toMatrix_rep_up_apply g ν μ)
    ((congrArg₂ (· * ·) (congrFun (congrFun (toMatrix_rep_downR g) a.2) l.2)
      (congrFun (congrFun (toMatrix_rep_downL g) a.1) l.1)).trans (mul_comm _ _))).symm

/-- For a family whose map is equivariant, the Lorentz invariants of the span of the family
  reduce to the span of the image under `liftComponents (T ∘ dualIndexEquiv)` of the Pauli tensor
  with dual Weyl indices, `dualWeylMap pauliTensor`. -/
noncomputable def invariantReductionToPauliValDualWeylOfComponents
    {repLorentz : Representation ℂ SL(2,ℂ) B} {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}
    (hT : complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents (T ∘ dualIndexEquiv))) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g)
      (Submodule.span ℂ (Set.range T)) :=
  (isEquivariant_comp_dualWeylMap hT).invariantReductionToSpanOfEq
    (complexLorentzTensor.hasReynolds _) invariants_up_upL_upR_eq_span_pauli
    (range_comp_dualWeylMap.trans (range_liftComponents_comp dualIndexEquiv T))
    (liftComponents (T ∘ dualIndexEquiv) (dualWeylMap pauliTensor)) rfl

end DualVectorComponents

/-!

### D.4. Once-derived one-index Weyl families and their products

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
      (liftComponents ((fun p => X p.2.1 * Y p.1 p.2.2) ∘ dualIndexEquiv)) :=
  isEquivariant_liftComponents_upDownRDownL _ fun g μ l => by
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
      (liftComponents ((fun p => X p.2.2 * Y p.1 p.2.1) ∘ dualIndexEquiv)) :=
  isEquivariant_liftComponents_upDownRDownL _ fun g μ l => by
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
