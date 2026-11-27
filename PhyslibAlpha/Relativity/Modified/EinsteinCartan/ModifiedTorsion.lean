/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Modified.EinsteinCartan.Contorsion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!

# Modified torsion and Cartan spin-torsion inversion

The modified torsion tensor and Cartan's algebraic spin-torsion equation in four dimensions.

## i. Overview

The modified torsion `S^k_{ij} = T^k_{ij} + δ^k_i T_{mj}{}^m - δ^k_j T_{mi}{}^m` is the combination
that appears in the Palatini variation. In four dimensions Cartan's equation `T = κ Ŝ + …` is
algebraically invertible, and vanishing spin implies vanishing torsion.

## ii. Key results

- `torsionTrace`, `modifiedTorsion` : torsion trace and modified torsion.
- `invertModifiedTorsion`, `cartan_algebraic_inversion` : 4D algebraic inversion.
- `cartan_vacuum_torsion_zero` : spinless vacuum has zero torsion.

## iii. Table of contents

- A. Cartan algebraic spin-torsion inversion in four dimensions

## iv. References

* Élie Cartan, *Sur une généralisation de la notion de courbure de Riemann et les espaces à
  torsion*, *Comptes Rendus de l'Académie des Sciences (Paris)* 174, pp. 593-595 (1922).
  [ref: Cartan1922]
* Friedrich W. Hehl et al., *General Relativity with Spin and Torsion: Foundations and Prospects*,
  *Reviews of Modern Physics* 48, pp. 393-416 (1976), Sec. II. [ref: Hehl1976]
* I. L. Shapiro, *Physical Aspects of the Space-Time Torsion*, *Physics Reports* 357, pp. 113-213
  (2002), Sec. 2 (https://arxiv.org/pdf/hep-th/0103093#page=4). [ref: Shapiro2002torsion]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace EinsteinCartan

/-!

## A. Cartan algebraic spin-torsion inversion in four dimensions

In four spacetime dimensions, Cartan's algebraic field equation `T̃^k_{ij} = κ spin^k_{ij}`
inverts linearly, forcing torsion to vanish identically in spinless vacuum.

-/

/-- Torsion vector trace `T_i = T^m_{im} = -T^m_{mi}` in four dimensions. -/
def torsionTrace (T : AffineConnection 4) (i : Fin 4) : ℝ := ∑ m : Fin 4, T m i m

/-- Modified torsion tensor entering the 4D Palatini variation of Einstein–Cartan theory:
`T̃^k_{ij} = T^k_{ij} + δ^k_i T^m_{jm} - δ^k_j T^m_{im}`. -/
def modifiedTorsion (T : AffineConnection 4) : AffineConnection 4 :=
  fun k i j => T k i j
    + (if k = i then torsionTrace T j else 0)
    - (if k = j then torsionTrace T i else 0)

/-- Antisymmetry of `modifiedTorsion` in its lower indices when `T` is antisymmetric. -/
lemma modifiedTorsion_antisymm (T : AffineConnection 4)
    (hT : ∀ k i j, T k i j = -T k j i) (k i j : Fin 4) :
    modifiedTorsion T k i j = -modifiedTorsion T k j i := by
  simp only [modifiedTorsion, hT k i j]
  ring

/-- In four dimensions, contracting the modified torsion gives `-2` times the torsion trace:
`∑ k, T̃^k_{ik} = -2 T^m_{im}`. -/
lemma torsionTrace_modifiedTorsion (T : AffineConnection 4) (i : Fin 4) :
    torsionTrace (modifiedTorsion T) i = -2 * torsionTrace T i := by
  simp only [torsionTrace, modifiedTorsion, Fin.sum_univ_four]
  fin_cases i <;> simp <;> ring

/-- Recovers the torsion `T` from the Palatini spin source `S = κ Σ` in four dimensions, by
`T^k_{ij} = S^k_{ij} + ½ (δ^k_i S^m_{jm} - δ^k_j S^m_{im})`; this inverts `modifiedTorsion`, that is,
the algebraic spin-torsion field equation of Einstein–Cartan theory. -/
noncomputable def invertModifiedTorsion (S : AffineConnection 4) : AffineConnection 4 :=
  fun k i j => S k i j
    + (1 / 2) * ((if k = i then torsionTrace S j else 0)
      - (if k = j then torsionTrace S i else 0))

/-- Applying `invertModifiedTorsion` to `modifiedTorsion T` recovers `T` identically. -/
lemma invertModifiedTorsion_modifiedTorsion (T : AffineConnection 4) :
    invertModifiedTorsion (modifiedTorsion T) = T := by
  ext k i j
  simp only [invertModifiedTorsion, torsionTrace_modifiedTorsion, modifiedTorsion]
  split_ifs <;> ring

/-- Applying `modifiedTorsion` to `invertModifiedTorsion S` recovers `S` identically. -/
lemma modifiedTorsion_invertModifiedTorsion (S : AffineConnection 4) :
    modifiedTorsion (invertModifiedTorsion S) = S := by
  have htr : ∀ j : Fin 4,
      torsionTrace (invertModifiedTorsion S) j = -(1 / 2) * torsionTrace S j := by
    intro j
    simp only [torsionTrace, invertModifiedTorsion, Fin.sum_univ_four]
    fin_cases j <;> simp <;> ring
  ext k i j
  simp only [modifiedTorsion, htr, invertModifiedTorsion]
  split_ifs <;> ring

/-- Cartan's algebraic spin-torsion field equation `T̃^k_{ij} = κ spin^k_{ij}` uniquely determines
spacetime torsion linearly in the spin density. -/
lemma cartan_algebraic_inversion (κ : ℝ) (T spin : AffineConnection 4)
    (hcartan : ∀ k i j, modifiedTorsion T k i j = κ * spin k i j) (k i j : Fin 4) :
    T k i j = κ * invertModifiedTorsion spin k i j := by
  have htr : torsionTrace (modifiedTorsion T) = fun m => κ * torsionTrace spin m := by
    ext m
    simp only [torsionTrace, hcartan]
    rw [Finset.mul_sum]
  have hinv := congrFun (congrFun (congrFun (invertModifiedTorsion_modifiedTorsion T) k) i) j
  rw [← hinv]
  simp only [invertModifiedTorsion, hcartan, htr]
  split_ifs <;> ring

/-- In spinless vacuum (`spin = 0`), Cartan's field equation forces torsion to vanish identically,
reducing Einstein–Cartan theory to torsion-free General Relativity. -/
lemma cartan_vacuum_torsion_zero (κ : ℝ) (T spin : AffineConnection 4)
    (hcartan : ∀ k i j, modifiedTorsion T k i j = κ * spin k i j)
    (hvac : ∀ k i j, spin k i j = 0) : T = 0 := by
  ext k i j
  rw [cartan_algebraic_inversion κ T spin hcartan k i j]
  simp [invertModifiedTorsion, torsionTrace, hvac]

end EinsteinCartan

end Modified

end GeneralRelativity
