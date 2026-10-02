/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Contraction.CrossToEnd
/-!

## Metrics as real Lorentz tensors

-/

@[expose] public section

open Module
open Matrix
open MatrixGroups
open TensorProduct

noncomputable section

namespace realLorentzTensor

/-!

## Definitions.

-/

/-- The metric `ηᵢᵢ` as a real Lorentz tensor. -/
abbrev coMetric (d : ℕ := 3) : ℝT[d, .down, .down] :=
  (realLorentzTensor d).metricTensor .down

/-- The metric `ηⁱⁱ` as a real Lorentz tensor. -/
abbrev contrMetric (d : ℕ := 3) : ℝT[d, .up, .up] :=
  (realLorentzTensor d).metricTensor .up

/-!

## Notation

-/

/-- The metric `ηᵢᵢ` as a real Lorentz tensors. -/
scoped[realLorentzTensor] notation "η'" => @coMetric

/-- The metric `ηⁱⁱ` as a real Lorentz tensors. -/
scoped[realLorentzTensor] notation "η" => @contrMetric

/-!

## Equivalent forms of the metrics

-/
open TensorSpecies
open Tensor

lemma coMetric_eq_fromConstPair {d : ℕ} :
    η' d = fromConstPair (S := realLorentzTensor d) (c1 := .down) (c2 := .down)
      (Lorentz.preCoMetric d) := by
  rfl

lemma contrMetric_eq_fromConstPair {d : ℕ} :
    η d = fromConstPair (S := realLorentzTensor d)
      (c1 := .up) (c2 := .up) (Lorentz.preContrMetric d) := by
  rfl

lemma coMetric_eq_fromPairT {d : ℕ} :
    η' d = fromPairT (S := realLorentzTensor d) (c1 := .down) (c2 := .down)
      (Lorentz.preCoMetricVal d) := by
  rw [coMetric_eq_fromConstPair, fromConstPair, Lorentz.preCoMetric_apply_one]

lemma contrMetric_eq_fromPairT {d : ℕ} :
    η d = fromPairT (S := realLorentzTensor d) (c1 := .up) (c2 := .up)
        (Lorentz.preContrMetricVal d) := by
  rw [contrMetric_eq_fromConstPair, fromConstPair, Lorentz.preContrMetric_apply_one]

/-

## Group actions

-/

/-- The tensor `coMetric` is invariant under the action of `LorentzGroup d`. -/
@[simp]
lemma actionT_coMetric {d : ℕ} (g : LorentzGroup d) :
    g • η' d = η' d:= by
  erw [TensorSpecies.metricTensor_invariant]

/-- The tensor `contrMetric` is invariant under the action of `LorentzGroup d`. -/
@[simp]
lemma actionT_contrMetric {d} (g : LorentzGroup d) : g • η d = η d := by
  erw [TensorSpecies.metricTensor_invariant]

/-

## Their value with respect to a basis

-/

lemma coMetric_repr_apply_eq_minkowskiMatrix {d : ℕ}
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.down, Color.down]) :
    (Tensor.basis _).repr (coMetric d) b =
    minkowskiMatrix (b 0) (b 1) := by
  change (Tensor.basis _).repr
    (metricTensor (S := realLorentzTensor d) Color.down) b = _
  rw [metricTensor_basis_repr,
    show ((realLorentzTensor d).metric Color.down) (1 : ℝ) = Lorentz.preCoMetricVal d from
      Lorentz.preCoMetric_apply_one,
    Lorentz.preCoMetricVal_expand_tmul_minkowskiMatrix]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single (b 0)] <;>
    simp +contextual [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply]

lemma contrMetric_repr_apply_eq_minkowskiMatrix {d : ℕ}
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.up, Color.up]) :
    (Tensor.basis _).repr (contrMetric d) b =
    minkowskiMatrix (b 0) (b 1) := by
  change (Tensor.basis _).repr
    (metricTensor (S := realLorentzTensor d) Color.up) b = _
  rw [metricTensor_basis_repr,
    show ((realLorentzTensor d).metric Color.up) (1 : ℝ) = Lorentz.preContrMetricVal d from
      Lorentz.preContrMetric_apply_one,
    Lorentz.preContrMetricVal_expand_tmul_minkowskiMatrix]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single (b 0)] <;>
    simp +contextual [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply]

/-- The component matrix of either real Lorentz metric tensor is the Minkowski matrix. -/
lemma metricTensor_repr_apply_eq_minkowskiMatrix {d : ℕ} (c : Color)
    (φ : ComponentIdx (S := realLorentzTensor d) ![c, c]) :
    (Tensor.basis _).repr (metricTensor (S := realLorentzTensor d) c) φ =
      minkowskiMatrix (φ 0) (φ 1) := by
  cases c with
  | up => exact contrMetric_repr_apply_eq_minkowskiMatrix φ
  | down => exact coMetric_repr_apply_eq_minkowskiMatrix φ

set_option backward.isDefEq.respectTransparency false in
/-- Raising or lowering one index of a real Lorentz tensor contracts that slot's components with
the Minkowski matrix. -/
lemma toDualMapAtIndex_basis_repr_apply {d n : ℕ} {c : Fin (n + 1) → Color}
    (i : Fin (n + 1)) (t : ℝT(d, c))
    (φ : ComponentIdx (S := realLorentzTensor d)
      (Function.update c i ((realLorentzTensor d).τ (c i)))) :
    (Tensor.basis _).repr (Tensor.toDualMapAtIndex (S := realLorentzTensor d) i t) φ =
      ∑ x : Fin 1 ⊕ Fin d,
        (Tensor.basis c).repr t (i.insertNth x (fun m => φ (i.succAbove m))) *
          minkowskiMatrix x (φ i) := by
  have h := crossToSlot_basis_repr_apply (S := realLorentzTensor d) i (0 : Fin 2) rfl
    (metricTensor (S := realLorentzTensor d) ((realLorentzTensor d).τ (c i))) t φ
  rw [crossToEnd_basis_repr_apply_eq_fin] at h
  simp only [basisIdxCongr_eq_refl, Equiv.refl_apply] at h
  refine h.trans (Finset.sum_congr rfl fun x _ => ?_)
  congr 1
  · congr 1
    funext m
    induction m using Fin.succAboveCases (i := i) with
    | x => rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
    | p q =>
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove,
        IsReindexing.inv_equiv_symm_eq,
        ← Fin.append_succAbove_const_eq_cycleIcc i, Fin.append_left]
  rw [metricTensor_repr_apply_eq_minkowskiMatrix]
  congr 1
  rw [show (1 : Fin 2) = (0 : Fin 2).succAbove 0 from rfl,
    Fin.insertNth_apply_succAbove, IsReindexing.inv_equiv_symm_eq,
    ← Fin.append_succAbove_const_eq_cycleIcc i, Fin.append_right]

/-- In the standard Lorentz basis, raising or lowering an index multiplies the component with that
index fixed by the corresponding diagonal entry of the Minkowski metric. -/
lemma toDualMapAtIndex_basis_repr_apply_eq_mul {d n : ℕ} {c : Fin (n + 1) → Color}
    (i : Fin (n + 1)) (t : ℝT(d, c))
    (φ : ComponentIdx (S := realLorentzTensor d)
      (Function.update c i ((realLorentzTensor d).τ (c i)))) :
    (Tensor.basis _).repr (Tensor.toDualMapAtIndex (S := realLorentzTensor d) i t) φ =
      (Tensor.basis c).repr t φ * minkowskiMatrix (φ i) (φ i) := by
  rw [toDualMapAtIndex_basis_repr_apply]
  change ((fun x => (Tensor.basis c).repr t
    (i.insertNth x (fun m => φ (i.succAbove m)))) ᵥ* minkowskiMatrix) (φ i) = _
  rw [minkowskiMatrix.vecMul_apply]
  congr 2
  change (i.insertNth (φ i) (i.removeNth φ) : Fin (n + 1) → Fin 1 ⊕ Fin d) = φ
  exact Fin.insertNth_self_removeNth i φ

end realLorentzTensor
