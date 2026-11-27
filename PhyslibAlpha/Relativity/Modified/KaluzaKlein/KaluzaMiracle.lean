/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import PhyslibAlpha.Relativity.Modified.KaluzaKlein.Basic
public import PhyslibAlpha.Relativity.Metrics.Basic
public import PhyslibAlpha.Relativity.Tensors.MaxwellStressEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Five-dimensional curvature reduction and Maxwell stress-energy

The Kaluza miracle `R^{(5)} = R^{(4)} - ¼ F_{ab} F^{ab}`, conformal tracelessness of
4D Maxwell stress-energy, and equivalence between 5D vacuum and 4D Einstein–Maxwell equations.

## i. Overview

At constant unit dilaton `φ = 1` on `D : KaluzaKleinData`, the horizontal Ricci tensor and
fifth-dimensional Ricci component combine to reduce the 5D scalar curvature `D.scalar5D` to the 4D
Einstein–Maxwell Lagrangian `R^{(4)} - ¼ F_{ab} F^{ab}`, and identify the horizontal 5D vacuum
Einstein equation with the 4D Einstein–Maxwell equations sourced by `maxwellStressEnergy`.

The reduction is carried out algebraically: the horizontal and fifth-dimensional Ricci components
`D.ricci5DHorizontal` and `D.ricci44` are defined directly by the stated component formulas rather
than derived from the 5D metric `D.metric` and the coordinate curvature operators, so
`KaluzaKleinData.kaluza_miracle` certifies the agreement of the postulated components with the 4D
Einstein–Maxwell scalar.

## ii. Key results

- `GeneralRelativity.maxwellFieldInvariant`, `GeneralRelativity.maxwellStressEnergy`,
  `GeneralRelativity.maxwellStressEnergy_trace_zero` (all in `Tensors/MaxwellStressEnergy.lean`) :
  4D Maxwell invariant, stress-energy tensor, and tracelessness.
- `KaluzaKleinData.ricci44`, `KaluzaKleinData.ricci5DHorizontal`, `KaluzaKleinData.scalar5D`,
  `KaluzaKleinData.kaluza_miracle` : Kaluza miracle scalar reduction on `KaluzaKleinData`.
- `KaluzaKleinData.einstein4D_eq_zero_iff` : equivalence of 5D vacuum and 4D Einstein–Maxwell
  equations.

## iii. Table of contents

- A. Five-dimensional curvature reduction and Maxwell stress-energy

## iv. References

* Theodor Kaluza, *Zum Unitätsproblem der Physik*, *Sitzungsberichte der Preußischen Akademie der
  Wissenschaften zu Berlin, Mathematisch-Physikalische Klasse* (1921), pp. 966-972.
  [ref: Kaluza1921]
* Oskar Klein, *Quantentheorie und fünfdimensionale Relativitätstheorie*, *Zeitschrift für Physik*
  37, pp. 895-906 (1926), Sec. 1-2. [ref: Klein1926]
* Oskar Klein, *The Atomicity of Electricity as a Quantum Theory Law*, *Nature* 118, p. 516 (1926).
  [ref: Klein1926Nature]
* J. M. Overduin and P. S. Wesson, *Kaluza-Klein Gravity*, *Physics Reports* 283, pp. 303-380
  (1997), Sec. 2 (https://arxiv.org/pdf/gr-qc/9805018#page=9). [ref: OverduinWesson1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace KaluzaKlein

/-!

## A. Five-dimensional curvature reduction and Maxwell stress-energy

Evaluating the constant-dilaton Kaluza–Klein Ricci components of a `KaluzaKleinData` splits the 5D
scalar curvature into the 4D Einstein–Hilbert term and the Maxwell gauge-field invariant.

-/

-- Factored out to isolate the scalar dimensional-reduction step of the Kaluza miracle.
/-- Fifth-dimension `(4, 4)` Kaluza–Klein Ricci component `R^{(5)}_{44} = ¼ F_{ab} F^{ab}` in
the constant unit-dilaton (`φ = 1`) compactification. -/
noncomputable def KaluzaKleinData.ricci44 (D : KaluzaKleinData) (F : Tensor2 4) : ℝ :=
  (1 / 4) * maxwellFieldInvariant D.M F

-- Factored out to separate the horizontal 4D curvature shift from the full 5D trace.
/-- Horizontal four-dimensional Kaluza–Klein Ricci tensor
`R^{(5)}_{ab} = R^{(4)}_{ab} - ½ g^{cd} F_{ac} F_{bd}` in the unit-dilaton (`φ = 1`)
compactification. -/
noncomputable def KaluzaKleinData.ricci5DHorizontal (D : KaluzaKleinData) (R4 : Tensor2 4)
    (F : Tensor2 4) (a b : Fin 4) : ℝ :=
  R4 a b - (1 / 2) * ∑ c : Fin 4, ∑ d : Fin 4, D.M.ginv c d * F a c * F b d

-- Packaged separately so `kaluza_miracle` states the 5D-to-4D curvature reduction cleanly.
/-- Five-dimensional Kaluza–Klein scalar curvature `R^{(5)} = g^{ab} R^{(5)}_{ab} + R^{(5)}_{44}`
in the unit-dilaton (`φ = 1`) compactification. -/
noncomputable def KaluzaKleinData.scalar5D (D : KaluzaKleinData) (R4 : Tensor2 4) (F : Tensor2 4) :
    ℝ :=
  (∑ a : Fin 4, ∑ b : Fin 4, D.M.ginv a b * D.ricci5DHorizontal R4 F a b) + D.ricci44 F

/-- The Kaluza miracle: the 5D Einstein–Hilbert scalar curvature `R^{(5)}` reduces identically to
the 4D Einstein–Maxwell Lagrangian `R^{(4)} - ¼ F_{ab} F^{ab}`. -/
lemma KaluzaKleinData.kaluza_miracle (D : KaluzaKleinData) (R4 : Tensor2 4) (F : Tensor2 4) :
    D.scalar5D R4 F =
      (∑ a : Fin 4, ∑ b : Fin 4, D.M.ginv a b * R4 a b) -
        (1 / 4) * maxwellFieldInvariant D.M F := by
  simp only [KaluzaKleinData.scalar5D, KaluzaKleinData.ricci5DHorizontal, KaluzaKleinData.ricci44,
    mul_sub, Finset.sum_sub_distrib]
  have hF :
      (∑ a : Fin 4, ∑ b : Fin 4,
        D.M.ginv a b * ((1 / 2) * ∑ c : Fin 4, ∑ d : Fin 4, D.M.ginv c d * F a c * F b d))
        = (1 / 2) * maxwellFieldInvariant D.M F := by
    have hpull :
        (∑ a : Fin 4, ∑ b : Fin 4,
          D.M.ginv a b * ((1 / 2) * ∑ c : Fin 4, ∑ d : Fin 4, D.M.ginv c d * F a c * F b d)) =
          (1 / 2) * metricTrace D.M
            (fun a b => ∑ c : Fin 4, ∑ d : Fin 4, D.M.ginv c d * F a c * F b d) := by
      simp only [metricTrace, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring_nf
    rw [hpull, metricTrace_maxwellQuad]
  rw [hF]
  ring

/-- Vanishing of the 5D horizontal Kaluza–Klein Einstein tensor `G^{(5)}_{ab} = R^{(5)}_{ab} -
½ g_{ab} R^{(5)} = 0` is equivalent to the 4D Einstein–Maxwell equation
`G^{(4)}_{ab} = ½ T^{EM}_{ab}`. -/
lemma KaluzaKleinData.einstein4D_eq_zero_iff (D : KaluzaKleinData) (R4 : Tensor2 4)
    (F : Tensor2 4) (a b : Fin 4) :
    D.ricci5DHorizontal R4 F a b - (1 / 2) * D.M.g a b * D.scalar5D R4 F = 0 ↔
      R4 a b - (1 / 2) * D.M.g a b * (∑ c : Fin 4, ∑ d : Fin 4, D.M.ginv c d * R4 c d) =
        (1 / 2) * GeneralRelativity.maxwellStressEnergy D.M F a b := by
  rw [D.kaluza_miracle]
  simp only [KaluzaKleinData.ricci5DHorizontal,
    GeneralRelativity.maxwellStressEnergy, GeneralRelativity.maxwellFieldInvariant]
  constructor <;> intro h <;> linarith

end KaluzaKlein

end Modified

end GeneralRelativity
