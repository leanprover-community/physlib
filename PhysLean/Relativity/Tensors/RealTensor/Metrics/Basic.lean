/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Basic
import PhysLean.Relativity.Tensors.MetricTensor
/-!

## Metrics as real Lorentz tensors

-/
open Module IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open TensorProduct
open IndexNotation

noncomputable section

namespace realLorentzTensor

/-!

## Definitions.

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensor. -/
abbrev coMetric (d : ℕ := 3) : ℝT[d, .down, .down] :=
  (realLorentzTensor d).metricTensor .down

/-- The metric `ηⁱⁱ` as a complex Lorentz tensor. -/
abbrev contrMetric (d : ℕ := 3) : ℝT[d, .up, .up] :=
  (realLorentzTensor d).metricTensor .up

/-!

## Notation

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensors. -/
scoped[realLorentzTensor] notation "η'" => @coMetric

/-- The metric `ηⁱⁱ` as a complex Lorentz tensors. -/
scoped[realLorentzTensor] notation "η" => @contrMetric

/-!

## Equivalent forms of the metrics

-/
open TensorSpecies
open Tensor

lemma coMetric_eq_fromConstPair {d : ℕ} :
    η' d = fromConstPair (Lorentz.preCoMetric d) := by
  rw [coMetric, metricTensor]
  rfl

lemma contrMetric_eq_fromConstPair {d : ℕ} :
    η d = fromConstPair (Lorentz.preContrMetric d) := by
  rw [contrMetric, metricTensor]
  rfl

lemma coMetric_eq_fromPairT {d : ℕ} :
    η' d = fromPairT (Lorentz.preCoMetricVal d) := by
  rw [coMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.preCoMetric_apply_one

lemma contrMetric_eq_fromPairT {d : ℕ} :
    η d = fromPairT (Lorentz.preContrMetricVal d) := by
  rw [contrMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.preContrMetric_apply_one

/-

## Group actions

-/

/-- The tensor `coMetric` is invariant under the action of `LorentzGroup d`. -/
@[simp]
lemma actionT_coMetric {d : ℕ} (g : LorentzGroup d) :
    g • η' d = η' d:= by
  rw [TensorSpecies.metricTensor_invariant]

/-- The tensor `contrMetric` is invariant under the action of `LorentzGroup d`. -/
@[simp]
lemma actionT_contrMetric {d} (g : LorentzGroup d) : g • η d = η d := by
  rw [TensorSpecies.metricTensor_invariant]

/-

## There value with respect to a basis

-/

lemma coMetric_repr_apply_eq_minkowskiMatrix {d : ℕ}
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.down, Color.down]) :
    (Tensor.basis _).repr (coMetric d) b =
    minkowskiMatrix (finSumFinEquiv.symm (b 0)) (finSumFinEquiv.symm (b 1)) := by
  rw [coMetric_eq_fromPairT]
  simp [Lorentz.preCoMetricVal]
  erw [Lorentz.coCoToMatrixRe_symm_expand_tmul]
  simp only [map_sum, _root_.map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue]
  conv_lhs =>
    enter [2, x1, 2, x2]
    rw [fromPairT_basis_repr]
    enter [2]
    change (((Lorentz.coBasisFin d).tensorProduct (Lorentz.coBasisFin d)).repr
      ((Lorentz.coBasis d) x1 ⊗ₜ[ℝ] (Lorentz.coBasis d) x2)) _
    simp [Fin.isValue, Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, Lorentz.coBasisFin]
    rw [Finsupp.single_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single (finSumFinEquiv.symm (b 0))]
  · rw [Finset.sum_eq_single (finSumFinEquiv.symm (b 1))]
    · simp
    · intro y _ hy
      simp only [Fin.isValue, Equiv.apply_symm_apply, ↓reduceIte, mul_one, mul_ite, mul_zero,
        ite_eq_right_iff]
      intro hy2
      rw [← hy2] at hy
      simp at hy
    · simp
  · intro y _ hy
    simp only [Fin.isValue, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Fintype.sum_sum_type,
      Finset.univ_unique, Fin.default_eq_zero, finSumFinEquiv_apply_left, Finset.sum_singleton,
      finSumFinEquiv_apply_right, Finset.sum_const_zero, ite_eq_right_iff]
    intro hy2
    rw [← hy2] at hy
    simp at hy
  · simp

lemma contrMetric_repr_apply_eq_minkowskiMatrix {d : ℕ}
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.up, Color.up]) :
    (Tensor.basis _).repr (contrMetric d) b =
    minkowskiMatrix (finSumFinEquiv.symm (b 0)) (finSumFinEquiv.symm (b 1)) := by
  rw [contrMetric_eq_fromPairT]
  simp [Lorentz.preContrMetricVal]
  erw [Lorentz.contrContrToMatrixRe_symm_expand_tmul]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Fin.isValue]
  conv_lhs =>
    enter [2, x1, 2, x2]
    rw [fromPairT_basis_repr]
    enter [2]
    change (((Lorentz.contrBasisFin d).tensorProduct (Lorentz.contrBasisFin d)).repr
      ((Lorentz.contrBasis d) x1 ⊗ₜ[ℝ] (Lorentz.contrBasis d) x2)) _
    simp [Fin.isValue, Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, Lorentz.contrBasisFin]
    rw [Finsupp.single_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single (finSumFinEquiv.symm (b 0))]
  · rw [Finset.sum_eq_single (finSumFinEquiv.symm (b 1))]
    · simp
    · intro y _ hy
      simp only [Fin.isValue, Equiv.apply_symm_apply, ↓reduceIte, mul_one, mul_ite, mul_zero,
        ite_eq_right_iff]
      intro hy2
      rw [← hy2] at hy
      simp at hy
    · simp
  · intro y _ hy
    simp only [Fin.isValue, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Fintype.sum_sum_type,
      Finset.univ_unique, Fin.default_eq_zero, finSumFinEquiv_apply_left, Finset.sum_singleton,
      finSumFinEquiv_apply_right, Finset.sum_const_zero, ite_eq_right_iff]
    intro hy2
    rw [← hy2] at hy
    simp at hy
  · simp

end realLorentzTensor
