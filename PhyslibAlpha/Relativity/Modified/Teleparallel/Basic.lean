/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Modified.EinsteinCartan
import Mathlib.Tactic.Ring

/-!

# Teleparallel gravity: Weitzenböck connection and torsion scalar

Orthonormal tetrads, curvature-free Weitzenböck affine connection, teleparallel torsion and
superpotential tensors, and quadratic torsion scalar `T`.

## i. Overview

In the Teleparallel Equivalent of General Relativity (TEGR), gravitational dynamics is formulated in
terms of an orthonormal tetrad `e^A_i` and its Weitzenböck connection `Γ^k_{ij} = e_A^k ∂_i e^A_j`
carrying torsion `T^k_{ij}` rather than curvature. This module defines `Tetrad`,
`Tetrad.weitzenbockConnection`, `Tetrad.weitzenbockTorsion`, `superpotential`, and `torsionScalar`,
decoupling the algebraic tetrad-torsion invariants from coordinate variational derivations so
cosmological FLRW and `f(T)` reductions can instantiate them directly.

## ii. Key results

- `Tetrad` : invertible tetrad frame `e^A_i` and inverse `e_A^i`.
- `Tetrad.weitzenbockConnection`, `Tetrad.mul_weitzenbockConnection`,
  `Tetrad.weitzenbockTorsion`, `Tetrad.weitzenbockTorsion_eq`,
  `Tetrad.weitzenbockTorsion_antisymm` : Weitzenböck connection and torsion tensor.
- `superpotential`, `superpotential_antisymm`, `torsionScalar` : teleparallel superpotential and
  quadratic torsion scalar `T`.

## iii. Table of contents

- A. Weitzenböck connection, torsion, and superpotential

## iv. References

* Albert Einstein, *Riemann-Geometrie mit Aufrechterhaltung des Begriffes des Fernparallelismus*,
  *Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-Mathematische Klasse*
  (1928), pp. 217-221. [ref: Einstein1928]
* Kenji Hayashi and Takeshi Shirafuji, *New General Relativity*, *Physical Review D* 19, pp.
  3524-3553 (1979), Sec. II-III. [ref: HayashiShirafuji1979]
* José W. Maluf, *The Teleparallel Equivalent of General Relativity*, *Annalen der Physik* (2013),
  Sec. 2-3 (https://arxiv.org/pdf/1303.3897#page=3). [ref: Maluf2013]
* Martin Krššák and Emmanuel N. Saridakis, *The Covariant Formulation of $f(T)$ Gravity*, *Classical
  and Quantum Gravity* (2016), Sec. 2 (https://arxiv.org/pdf/1510.08432#page=3).
  [ref: KrssakSaridakis2016]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Teleparallel

open GeneralRelativity.Modified.EinsteinCartan

/-!

## A. Weitzenböck connection, torsion, and superpotential

A tetrad coframe and its inverse define the curvature-free Weitzenböck connection, whose torsion
contracts with the teleparallel superpotential to form the torsion scalar `T`.

-/

/-- An orthonormal tetrad (vielbein) frame `e^A_i` paired with its inverse `e_A^i` in `n`
dimensions. -/
structure Tetrad (n : ℕ) where
  /-- Coframe tetrad components `e^A_i`. -/
  e : Tensor2 n
  /-- Inverse frame components `e_A^i` stored as `einv i A`. -/
  einv : Tensor2 n
  /-- Left-to-right inverse relation `e * einv = 1`. -/
  inv_left : e * einv = 1
  /-- Right-to-left inverse relation `einv * e = 1`. -/
  inv_right : einv * e = 1

namespace Tetrad

/-- Weitzenböck affine connection `Γ^k_{ij} = ∑_A e_A^k ∂_i e^A_j` constructed from a tetrad
and coframe partial derivatives `∂_i e^A_j`, satisfying `e * Γ_i = ∂_i e`. -/
def weitzenbockConnection {n : ℕ} (T : Tetrad n) (de : Fin n → Tensor2 n) :
    AffineConnection n :=
  fun k i j => ∑ A : Fin n, T.einv k A * de i A j

/-- Left-multiplication by the coframe recovers the tetrad derivative:
`e^A_k Γ^k_{ij} = ∂_i e^A_j`. -/
lemma mul_weitzenbockConnection {n : ℕ} (T : Tetrad n) (de : Fin n → Tensor2 n) (i : Fin n) :
    T.e * Matrix.of (fun k j => T.weitzenbockConnection de k i j) = de i := by
  ext a j
  rw [Matrix.mul_apply]
  have hswap : (∑ k : Fin n, T.e a k * ∑ A : Fin n, T.einv k A * de i A j) =
      ∑ A : Fin n, (∑ k : Fin n, T.e a k * T.einv k A) * de i A j := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hinv : ∀ A : Fin n, (∑ k : Fin n, T.e a k * T.einv k A) = if a = A then 1 else 0 := by
    intro A
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun T.inv_left a) A
  simp [weitzenbockConnection, hswap, hinv]

/-- Weitzenböck torsion tensor `T^k_{ij} = Γ^k_{ij} - Γ^k_{ji}`. -/
def weitzenbockTorsion {n : ℕ} (T : Tetrad n) (de : Fin n → Tensor2 n) :
    AffineConnection n :=
  torsion (T.weitzenbockConnection de)

/-- Explicit tetrad-derivative formula for the Weitzenböck torsion:
`T^k_{ij} = ∑_A e_A^k (∂_i e^A_j - ∂_j e^A_i)`. -/
lemma weitzenbockTorsion_eq {n : ℕ} (T : Tetrad n) (de : Fin n → Tensor2 n) (k i j : Fin n) :
    T.weitzenbockTorsion de k i j = ∑ A : Fin n, T.einv k A * (de i A j - de j A i) := by
  simp only [weitzenbockTorsion, torsion, weitzenbockConnection, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun A _ => by ring

/-- Antisymmetry of the Weitzenböck torsion in its lower indices:
`T^k_{ij} = -T^k_{ji}`. -/
lemma weitzenbockTorsion_antisymm {n : ℕ} (T : Tetrad n) (de : Fin n → Tensor2 n)
    (k i j : Fin n) :
    T.weitzenbockTorsion de k i j = -T.weitzenbockTorsion de k j i :=
  torsion_antisymm (T.weitzenbockConnection de) k i j

end Tetrad

/-- Covariant teleparallel superpotential
`S_{k i j} = ¼ (T_{kij} + T_{jik} - T_{ijk}) + ½ (g_{ki} T^m_{jm} - g_{kj} T^m_{im})`,
antisymmetric in its last two indices `(i, j)` and contracting with torsion as
`T = S_k^{ij} T^k_{ij}`. -/
noncomputable def superpotential (M : MetricTensor 4) (T : AffineConnection 4) :
    AffineConnection 4 :=
  fun k i j =>
    (1 / 4) *
      ((∑ p : Fin 4, M.g k p * T p i j)
        + (∑ p : Fin 4, M.g j p * T p i k)
        - (∑ p : Fin 4, M.g i p * T p j k))
      + (1 / 2) * (M.g k i * torsionTrace T j - M.g k j * torsionTrace T i)

/-- Antisymmetry of the teleparallel superpotential in its last two indices `(i, j)` whenever
`T` is antisymmetric in its lower indices. -/
lemma superpotential_antisymm (M : MetricTensor 4) (T : AffineConnection 4)
    (hT : ∀ k i j, T k i j = -T k j i) (k i j : Fin 4) :
    superpotential M T k i j = -superpotential M T k j i := by
  simp only [superpotential]
  have hsum : (∑ p : Fin 4, M.g k p * T p i j) = -(∑ p : Fin 4, M.g k p * T p j i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => by rw [hT p i j]; ring
  rw [hsum]
  ring

/-- Quadratic teleparallel torsion scalar `T = ∑_{k,i,j} S_k^{ij} T^k_{ij}` formed by
contracting the superpotential with the torsion tensor. -/
noncomputable def torsionScalar (M : MetricTensor 4) (T : AffineConnection 4) : ℝ :=
  ∑ k : Fin 4, ∑ p : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
    M.ginv k p * superpotential M T p i j *
      (∑ q : Fin 4, ∑ r : Fin 4, M.ginv i q * M.ginv j r *
        (∑ s : Fin 4, M.g k s * T s q r))

end Teleparallel

end Modified

end GeneralRelativity
