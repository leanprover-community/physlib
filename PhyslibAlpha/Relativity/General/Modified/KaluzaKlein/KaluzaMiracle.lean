/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import PhyslibAlpha.Relativity.Metrics.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Five-dimensional curvature reduction and Maxwell stress-energy

The Kaluza miracle `R^{(5)} = R^{(4)} - ¼ F_{ab} F^{ab}`, conformal tracelessness of
4D Maxwell stress-energy, and equivalence between 5D vacuum and 4D Einstein–Maxwell equations.

## i. Overview

At constant unit dilaton `φ = 1`, the horizontal Ricci tensor and fifth-dimensional Ricci component
combine to reduce the 5D scalar curvature `kkScalar5D` to the 4D Einstein–Maxwell Lagrangian
`R^{(4)} - ¼ F_{ab} F^{ab}`, and identify the horizontal 5D vacuum Einstein equation with the
4D Einstein–Maxwell equations sourced by `maxwellStressEnergy`.

## ii. Key results

- `maxwellF2`, `maxwellStressEnergy`, `maxwellStressEnergy_trace_zero` : 4D Maxwell invariant,
  stress-energy tensor, and tracelessness.
- `kkRicci44`, `kkRicci4D`, `kkScalar5D`, `kkScalar5D_eq` : Kaluza miracle scalar reduction.
- `kkEinstein4D_eq_zero_iff` : equivalence of 5D vacuum and 4D Einstein–Maxwell equations.

## iii. Table of contents

- A. Five-dimensional curvature reduction and Maxwell stress-energy

## iv. References

* Theodor Kaluza, *Zum Unitätsproblem der Physik*, *Sitzungsberichte der Preu\ssischen Akademie
  der Wissenschaften zu Berlin, Mathematisch-Physikalische Klasse* (1921). [ref: Kaluza1921]
* Oskar Klein, *Quantentheorie und fünfdimensionale Relativitätstheorie*, *Zeitschrift für Physik*
  (1926). [ref: Klein1926]
* Oskar Klein, *The Atomicity of Electricity as a Quantum Theory Law*, *Nature* (1926). [ref:
  Klein1926Nature]

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace KaluzaKlein

/-!

## A. Five-dimensional curvature reduction and Maxwell stress-energy

-/

/-- Four-dimensional Maxwell field-strength quadratic invariant `F_{ab} F^{ab} = g^{ac} g^{bd}
F_{ab} F_{cd}`. -/
def maxwellF2 (M : MetricTensor 4) (F : Tensor2 4) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, M.ginv a c * M.ginv b d * F a b * F c d

/-- Four-dimensional electromagnetic stress-energy tensor
`T^{EM}_{ab} = g^{cd} F_{ac} F_{bd} - ¼ g_{ab} F_{cd} F^{cd}`. -/
noncomputable def maxwellStressEnergy (M : MetricTensor 4) (F : Tensor2 4) (a b : Fin 4) : ℝ :=
  (∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d) - (1 / 4) * M.g a b * maxwellF2 M F

/-- In four spacetime dimensions (`d = 4`), the Maxwell stress-energy tensor is identically
trace-free: `g^{ab} T^{EM}_{ab} = 0`. -/
lemma maxwellStressEnergy_trace_zero (M : MetricTensor 4) (F : Tensor2 4) :
    (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * maxwellStressEnergy M F a b) = 0 := by
  have htr_g : (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * M.g a b) = 4 := by
    have hdiag : ∀ a : Fin 4, (∑ b : Fin 4, M.ginv a b * M.g a b) = 1 := by
      intro a
      have h1 : (∑ b : Fin 4, M.ginv a b * M.g a b) = ∑ b : Fin 4, M.ginv a b * M.g b a :=
        Finset.sum_congr rfl fun b _ => by rw [M.symm a b]
      rw [h1]
      have h := congrFun (congrFun M.inv_right a) a
      simpa [Matrix.mul_apply, Matrix.one_apply] using h
    simp [hdiag]
  unfold maxwellStressEnergy
  simp only [mul_sub, Finset.sum_sub_distrib]
  have h1 :
      (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b *
        (∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d))
        = maxwellF2 M F := by
    unfold maxwellF2
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun d _ => by ring
  have h2 :
      (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * ((1 / 4) * M.g a b * maxwellF2 M F))
        = (1 / 4) * (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * M.g a b) * maxwellF2 M F := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h1, h2, htr_g]
  ring

/-- Fifth-dimension `(4, 4)` Kaluza–Klein Ricci component at unit dilaton `φ = 1`:
`R^{(5)}_{44} = ¼ F_{ab} F^{ab}`. -/
noncomputable def kkRicci44 (M : MetricTensor 4) (F : Tensor2 4) : ℝ :=
  (1 / 4) * maxwellF2 M F

/-- Horizontal 4D Kaluza–Klein Ricci components at unit dilaton `φ = 1`:
`R^{(5)}_{ab} = R^{(4)}_{ab} - ½ g^{cd} F_{ac} F_{bd}`. -/
noncomputable def kkRicci4D (M : MetricTensor 4) (R4 : Tensor2 4) (F : Tensor2 4)
    (a b : Fin 4) : ℝ :=
  R4 a b - (1 / 2) * ∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d

/-- Five-dimensional Kaluza–Klein scalar curvature `R^{(5)} = g^{ab} R^{(5)}_{ab} + R^{(5)}_{44}` at
unit dilaton `φ = 1`. -/
noncomputable def kkScalar5D (M : MetricTensor 4) (R4 : Tensor2 4) (F : Tensor2 4) : ℝ :=
  (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * kkRicci4D M R4 F a b) + kkRicci44 M F

/-- The Kaluza miracle: the 5D Einstein–Hilbert scalar curvature `R^{(5)}` reduces identically to
the 4D Einstein–Maxwell Lagrangian `R^{(4)} - ¼ F_{ab} F^{ab}`. -/
lemma kkScalar5D_eq (M : MetricTensor 4) (R4 : Tensor2 4) (F : Tensor2 4) :
    kkScalar5D M R4 F =
      (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * R4 a b) - (1 / 4) * maxwellF2 M F := by
  unfold kkScalar5D kkRicci4D kkRicci44
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hF :
      (∑ a : Fin 4, ∑ b : Fin 4,
        M.ginv a b * ((1 / 2) * ∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d))
        = (1 / 2) * maxwellF2 M F := by
    unfold maxwellF2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun d _ => by ring
  rw [hF]
  ring

/-- Vanishing of the 5D horizontal Kaluza–Klein Einstein tensor `G^{(5)}_{ab} = R^{(5)}_{ab} -
½ g_{ab} R^{(5)} = 0` is equivalent to the 4D Einstein–Maxwell equation
`G^{(4)}_{ab} = ½ T^{EM}_{ab}`. -/
lemma kkEinstein4D_eq_zero_iff (M : MetricTensor 4) (R4 : Tensor2 4) (F : Tensor2 4)
    (a b : Fin 4) :
    kkRicci4D M R4 F a b - (1 / 2) * M.g a b * kkScalar5D M R4 F = 0 ↔
      R4 a b - (1 / 2) * M.g a b * (∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * R4 c d) =
        (1 / 2) * maxwellStressEnergy M F a b := by
  rw [kkScalar5D_eq]
  unfold kkRicci4D maxwellStressEnergy
  constructor <;> intro h <;> linarith

end KaluzaKlein

end Modified

end GeneralRelativity
