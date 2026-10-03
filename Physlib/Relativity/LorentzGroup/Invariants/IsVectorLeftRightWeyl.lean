/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.RankTwo
public import Physlib.Relativity.PauliMatrices.ToTensor
/-!
# Lorentz invariants of a four-vector index and a left-right Weyl pair

## i. Overview

A family `T^{μ α α'}` carrying one four-vector index and one opposite-chirality Weyl pair is an
equivariant linear map `f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B`, `IsVectorLeftRightWeyl` (A). Every
Lorentz invariant in the range of `f` is a multiple of `f σ^^^`, the image of the Pauli
matrices as a tensor, the shape of the fermion kinetic term `ψ̄_{α'} σ̄^{μ α' α} ∂_μ ψ_α`. That is
`IsVectorLeftRightWeyl.exists_smul_map_pauliMatrix_add_of_invariant`, stated modulo a
Lorentz-stable submodule `S`, and packaged as `IsVectorLeftRightWeyl.invariantReductionToSpan`
(D).

An opposite-chirality Weyl pair carries the `(1/2, 1/2)` representation, which is the
four-vector representation, so the three indices are two four-vector indices, and two of those
admit only the metric. The proof makes that literal. The components `f (e_μ ⊗ e_α ⊗ e_α')` of `f`
move as `T^{μ α α'}` (B); contracting their Weyl pair against the covariant Pauli matrices
`PauliMatrix.pauliLower`, which intertwine the two index laws (`SL2C.sum_pauliLower_mul_sl2c`),
gives a family `vectorPair f` of two four-vector indices, whose map is equivariant, whose range
is the range of `f` by Fierz completeness, and which sends the metric to `f σ^^^` (C); `RankTwo`
supplies the classification (D). A family of components is turned back into a map by
`ofVectorComponents` (E).

The Standard Model's fermion symbols are `Module.Dual`-valued, so their spinor indices are dual
Weyl indices: an equivariant map out of `ℂT[.up, .downR, .downL]`, `IsVectorDualLeftRightWeyl`.
Dualising both Weyl indices, `dualWeylMap`, is an equivariant surjection from
`ℂT[.up, .upL, .upR]` carrying `σ^^^` to `σ^__`, so every invariant in the range of such a map is
a multiple of `f σ^__` (F). A family of dual components is turned into a map by
`ofDualVectorComponents` (G).

## ii. Key results

- `Lorentz.IsVectorLeftRightWeyl.invariantReductionToSpan` : the invariants reduce to `f σ^^^`.
- `Lorentz.dualWeylMap` : the dualisation of the Weyl indices.
- `Lorentz.IsVectorDualLeftRightWeyl.invariantReductionToSpan` : the invariants reduce to
  `f σ^__`.

## iii. Table of contents

- A. Vector-Weyl families as equivariant maps
- B. The components of an equivariant map
- C. The reduction to a pair of four-vector indices
- D. The classification of the Lorentz invariants
- E. Maps from components
- F. Dual Weyl indices
- G. Maps from dual components

-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C complexLorentzTensor

/-!

## A. Vector-Weyl families as equivariant maps

-/

/-- A family with a four-vector index and a left- and a right-handed Weyl index `T^{μ α α'}`:
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

## B. The components of an equivariant map

The components `f (e_μ ⊗ e_α ⊗ e_α')` of an equivariant map are moved by the Lorentz matrix on
the vector index, by the matrix of `g` on the left Weyl index and by its complex conjugate on
the right one.

-/

include hf in
/-- The components of an equivariant map are moved as `T^{μ α α'}`, the summed index first in
  each factor. -/
lemma repLorentz_map_indexBasis (g : SL(2,ℂ)) (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) :
    repLorentz g (f (indexBasis d)) = ∑ e : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      ((((SL2C.toLorentzGroup g).1 e.1 d.1 : ℝ) : ℂ)
        * (g.1 e.2.1 d.2.1 * star (g.1 e.2.2 d.2.2))) • f (indexBasis e) := by
  rw [indexBasis_apply, ← hf.equivariant, TensorSpecies.smul_basis_eq_sum, map_sum,
    ← indexEquiv.symm.sum_comp]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul, Fin.prod_univ_three, mul_assoc, indexBasis_apply]
  exact congrArg (· • _) (congrArg₂ (· * ·) (toMatrix_rep_up_apply g e.1 d.1)
    (congrArg₂ (· * ·) (congrFun (congrFun (toMatrix_rep_upL g) e.2.1) d.2.1)
      (congrFun (congrFun (toMatrix_rep_upR g) e.2.2) d.2.2)))

include hf in
/-- Moving a contraction of the Weyl pair at vector index `μ`: the vector index moves by the
  Lorentz matrix and the coefficients of the Weyl pair by the matrix of `g` and its complex
  conjugate. -/
lemma repLorentz_sum_smul (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (c : Fin 2 × Fin 2 → ℂ) :
    repLorentz g (∑ a : Fin 2 × Fin 2, c a • f (indexBasis (μ, a)))
      = ∑ ν : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
        • ∑ q : Fin 2 × Fin 2, (∑ d : Fin 2 × Fin 2, c d * (g.1 q.1 d.1 * star (g.1 q.2 d.2)))
          • f (indexBasis (ν, q)) := by
  rw [(repLorentz g).map_sum_smul_of_forall_eq (fun a => f (indexBasis (μ, a)))
    (fun e => f (indexBasis e))
    (fun e a => (((SL2C.toLorentzGroup g).1 e.1 μ : ℝ) : ℂ)
      * (g.1 e.2.1 a.1 * star (g.1 e.2.2 a.2)))
    (fun a => hf.repLorentz_map_indexBasis g (μ, a)) c, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul, Finset.mul_sum]
  exact congrArg (· • f (indexBasis (ν, q))) (Finset.sum_congr rfl fun p _ => by ring)

/-!

## C. The reduction to a pair of four-vector indices

Contracting the Weyl pair of the components against the covariant Pauli matrices gives a
family `vectorPair f` of two four-vector indices, whose map `ofComponents (vectorPair f)` is a
rank-two Lorentz family. By Fierz completeness the contraction is invertible, so its span is the
range of `f`, and the image of the metric under its map is `f σ^^^`.

-/

/-- The family of two four-vector indices obtained by contracting the Weyl pair of the
  components of `f` against the covariant Pauli matrices. -/
noncomputable def vectorPair (f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B) :
    (Fin 2 → Fin 1 ⊕ Fin 3) → B :=
  fun d => ∑ a : Fin 2 × Fin 2, PauliMatrix.pauliLower (d 1) a.1 a.2 • f (indexBasis (d 0, a))

include hf in
/-- The reduced family is a rank-two Lorentz family: the intertwining identity
  `SL2C.sum_pauliLower_mul_sl2c` carries the Weyl pair into a second vector index. -/
lemma isLorentzCovariant_vectorPair :
    IsLorentzCovariant 2 B repLorentz (ofComponents (vectorPair f)) := by
  refine (isLorentzCovariant_ofComponents_iff _).2 fun g l => ?_
  rw [vectorPair, hf.repLorentz_sum_smul, sum_pi_fin_two]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [sum_pauliLower_mul_sl2c]
  rw [Fintype.sum_sum_mul_smul
    (fun (q : Fin 2 × Fin 2) (ρ : Fin 1 ⊕ Fin 3) => PauliMatrix.pauliLower ρ q.1 q.2)
    (fun ρ => (((SL2C.toLorentzGroup g).1 ρ (l 1) : ℝ) : ℂ))
    (fun q => f (indexBasis (ν, q))), Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [vectorPair, smul_smul, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- The reduction is invertible: by the Fierz completeness relation each component of `f` is
  recovered from the reduced family. -/
lemma map_indexBasis_eq_sum_vectorPair (f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B)
    (μ : Fin 1 ⊕ Fin 3) (b : Fin 2 × Fin 2) :
    f (indexBasis (μ, b)) = ∑ ρ : Fin 1 ⊕ Fin 3,
      ((2 : ℂ)⁻¹ * PauliMatrix.pauliLower ρ b.2 b.1) • vectorPair f ![μ, ρ] := by
  calc f (indexBasis (μ, b)) = ∑ a : Fin 2 × Fin 2,
        ((if a.1 = b.1 then (1 : ℂ) else 0) * (if a.2 = b.2 then 1 else 0))
          • f (indexBasis (μ, a)) := by
        rw [Fintype.sum_prod_type]
        simp [ite_smul, Finset.sum_ite_eq']
    _ = ∑ a : Fin 2 × Fin 2, (∑ ρ : Fin 1 ⊕ Fin 3,
          (2 : ℂ)⁻¹ * PauliMatrix.pauliLower ρ b.2 b.1 * PauliMatrix.pauliLower ρ a.1 a.2)
            • f (indexBasis (μ, a)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        rw [show (∑ ρ : Fin 1 ⊕ Fin 3,
              (2 : ℂ)⁻¹ * PauliMatrix.pauliLower ρ b.2 b.1 * PauliMatrix.pauliLower ρ a.1 a.2)
            = (2 : ℂ)⁻¹ * ∑ ρ : Fin 1 ⊕ Fin 3,
              PauliMatrix.pauliLower ρ b.2 b.1 * PauliMatrix.pauliLower ρ a.1 a.2 from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ρ _ => (mul_assoc _ _ _),
          PauliMatrix.sum_pauliLower_mul_pauliLower a.1 a.2 b.1 b.2]
        field_simp
    _ = _ := by
        simp only [vectorPair, Matrix.cons_val_zero, Matrix.cons_val_one,
          Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_smul

/-- The reduction does not change the span: the reduced family spans the range of `f`. -/
lemma span_range_vectorPair (f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B) :
    Submodule.span ℂ (Set.range (vectorPair f)) = LinearMap.range f := by
  refine le_antisymm (Submodule.span_le.2 <| Set.range_subset_iff.2 fun d =>
    sum_mem fun a _ => Submodule.smul_mem _ _ (LinearMap.mem_range_self f _)) ?_
  rw [← Submodule.map_top, ← indexBasis.span_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨⟨μ, b⟩, rfl⟩, rfl⟩
  rw [map_indexBasis_eq_sum_vectorPair]
  exact sum_mem fun ρ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The image of the metric under the map of the reduced family is the image `f σ^^^` of the
  Pauli tensor: the two lowerings of the vector index cancel, so no sign and no scalar appear. -/
lemma ofComponents_vectorPair_metric (f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B) :
    ofComponents (vectorPair f) RankTwo.metric = f σ^^^ := by
  rw [RankTwo.ofComponents_metric, sum_pi_fin_two, toTensor_eq_sum_indexBasis, map_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_eq_single ν (fun ρ _ hρ => ?_) (fun hν => absurd (Finset.mem_univ ν) hν)]
  · simp only [vectorPair, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.smul_sum,
      smul_smul, map_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [PauliMatrix.pauliLower_eq_smul, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    rcases ν with ν | ν <;> fin_cases ν <;> norm_num [minkowskiMatrixZ]
  · rw [show minkowskiMatrixZ (![ν, ρ] 0) (![ν, ρ] 1) = 0 from by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      simp [minkowskiMatrixZ, Ne.symm hρ]]
    simp

/-!

## D. The classification of the Lorentz invariants

`RankTwo` classifies the invariants of the range of `ofComponents (vectorPair f)`, which is the
range of `f`, and the image of the metric under it is `f σ^^^`.

-/

include hf in
/-- The image `f σ^^^` of the Pauli tensor is Lorentz invariant. -/
lemma repLorentz_map_pauliMatrix (g : SL(2,ℂ)) : repLorentz g (f σ^^^) = f σ^^^ :=
  hf.rep_map_of_invariant toTensor_smul_eq_self g

include hf in
/-- Every Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is a
  multiple of the image `f σ^^^` of the Pauli tensor plus an element of `S`: the shape of the
  fermion kinetic term. -/
lemma exists_smul_map_pauliMatrix_add_of_invariant (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ LinearMap.range f ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • f σ^^^ + y := by
  obtain ⟨a, y, hy, ha⟩ := RankTwo.exists_smul_map_metric_add_of_invariant
    hf.isLorentzCovariant_vectorPair S hS
    (by rwa [range_ofComponents, span_range_vectorPair]) hinv
  exact ⟨a, y, hy, by rwa [ofComponents_vectorPair_metric] at ha⟩

include hf in
/-- The Lorentz invariants of the range of `f` reduce to the span of the image `f σ^^^` of the
  Pauli tensor. -/
noncomputable def invariantReductionToSpan :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) where
  spanningVector := f σ^^^
  stable := hf.isStableUnder_range
  spanningVector_fixed := hf.repLorentz_map_pauliMatrix
  reduce S hS _ hx hinv := hf.exists_smul_map_pauliMatrix_add_of_invariant S hS hx hinv

end IsVectorLeftRightWeyl

/-!

## E. Maps from components

A family `T (μ, α, α')` of vectors is the linear map `ofVectorComponents T` sending
`e_μ ⊗ e_α ⊗ e_α'` to `T (μ, α, α')`, and it is equivariant when the vectors are moved as the
basis tensors are.

-/

section VectorComponents

open PauliMatrix TensorSpecies

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The linear map out of `ℂT[.up, .upL, .upR]` sending `e_μ ⊗ e_α ⊗ e_α'` to
  `T (μ, α, α')`. -/
noncomputable def ofVectorComponents (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) :
    ℂT[.up, .upL, .upR] →ₗ[ℂ] B :=
  indexBasis.constr ℂ T

@[simp]
lemma ofVectorComponents_indexBasis (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)
    (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) : ofVectorComponents T (indexBasis d) = T d :=
  indexBasis.constr_basis ℂ T d

/-- The range of `ofVectorComponents T` is the span of the vectors `T d`. -/
lemma range_ofVectorComponents (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) :
    LinearMap.range (ofVectorComponents T) = Submodule.span ℂ (Set.range T) :=
  indexBasis.constr_range ℂ

/-- `ofVectorComponents T` is equivariant when `T (μ, α, α')` is moved as `T^{μ α α'}`: the
  vector index by the Lorentz matrix, the left index by the matrix of `g` and the right index by
  its complex conjugate, the summed index first in each factor. -/
lemma isVectorLeftRightWeyl_ofVectorComponents {repLorentz : Representation ℂ SL(2,ℂ) B}
    (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)
    (hT : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
      repLorentz g (T (μ, l)) = ∑ (ν : Fin 1 ⊕ Fin 3), ∑ (a : Fin 2 × Fin 2),
        ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
          * (g.1 a.1 l.1 * star (g.1 a.2 l.2))) • T (ν, a)) :
    IsVectorLeftRightWeyl B repLorentz (ofVectorComponents T) := by
  have h : ofVectorComponents T
      = (Tensor.basis ![Color.up, Color.upL, Color.upR]).constr ℂ fun φ => T (indexEquiv φ) :=
    (Tensor.basis (S := complexLorentzTensor) _).ext fun φ => by
      rw [Module.Basis.constr_basis, ← indexEquiv.symm_apply_apply φ, ← indexBasis_apply,
        ofVectorComponents_indexBasis, Equiv.apply_symm_apply]
  rw [h]
  refine TensorSpecies.isEquivariant_constr _ fun g φ => ?_
  obtain ⟨⟨μ, l⟩, rfl⟩ := indexEquiv.symm.surjective φ
  rw [Equiv.apply_symm_apply, hT, ← indexEquiv.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Equiv.apply_symm_apply, Fin.prod_univ_three, mul_assoc]
  exact congrArg (· • _) (congrArg₂ (· * ·) (toMatrix_rep_up_apply g ν μ)
    (congrArg₂ (· * ·) (congrFun (congrFun (toMatrix_rep_upL g) a.1) l.1)
      (congrFun (congrFun (toMatrix_rep_upR g) a.2) l.2))).symm

end VectorComponents

/-!

## F. Dual Weyl indices

A family `T^μ{}_{α' α}` with a four-vector index and a dual right- and a dual left-handed Weyl
index is an equivariant map out of `ℂT[.up, .downR, .downL]`, `IsVectorDualLeftRightWeyl`.
Dualising both Weyl indices, `dualWeylMap`, is an equivariant surjection out of
`ℂT[.up, .upL, .upR]` which carries `σ^^^` to `σ^__`, so composing with it turns such a family
into an `IsVectorLeftRightWeyl` family with the same range, and section D applies.

-/

/-- A family with a four-vector index and a dual right- and a dual left-handed Weyl index
  `T^μ{}_{α' α}`: an equivariant linear map out of `ℂT[.up, .downR, .downL]`. -/
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
/-- Dualising the Weyl indices is surjective: the dualisations are inverted by raising the
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
  `S`: the kinetic term of a Weyl fermion. -/
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

## G. Maps from dual components

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
  toFun v := (finSumFinEquiv.symm (v 0 : Fin 4), v 2, v 1)
  invFun v := fun | 0 => finSumFinEquiv v.1 | 1 => v.2.2 | 2 => v.2.1
  left_inv v := by
    funext x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Equiv.apply_symm_apply]
    fin_cases x
    <;> rfl
  right_inv v := by
    simp

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

/-- `ofDualVectorComponents T` is equivariant when `T (μ, α, α')` is moved as `T^μ{}_{α α'}`: the
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

end Lorentz
