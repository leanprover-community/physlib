/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Modified.EinsteinCartan
import Mathlib.Tactic.Ring

/-!

# Teleparallel gravity: Weitzenböck connection and torsion scalar

Orthonormal tetrads, curvature-free Weitzenböck affine connection, teleparallel torsion and
superpotential tensors, and quadratic torsion scalar `T`.

## i. Overview

In the Teleparallel Equivalent of General Relativity (TEGR), gravitational dynamics is formulated in
terms of an orthonormal tetrad `e^A_i` and its Weitzenböck connection `Γ^k_{ij} = e_A^k ∂_i e^A_j`
carrying torsion `T^k_{ij}` rather than curvature. This module defines `Tetrad`,
`weitzenbockConn`, `weitzenbockTorsion`, `superpotential`, and `torsionScalar`, decoupling the
algebraic tetrad-torsion invariants from coordinate variational derivations so cosmological FLRW
and `f(T)` reductions can instantiate them directly.

## ii. Key results

- `Tetrad` : invertible tetrad frame `e^A_i` and inverse `e_A^i`.
- `weitzenbockConn`, `weitzenbockTorsion`, `weitzenbockTorsion_eq`,
  `weitzenbockTorsion_antisymm` : Weitzenböck connection and torsion tensor.
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

-/

/-- An orthonormal tetrad (vielbein) frame `e^A_i` paired with its inverse `e_A^i` in `n`
dimensions. -/
structure Tetrad (n : ℕ) where
  /-- Coframe tetrad components `e^A_i`. -/
  e : Tensor2 n
  /-- Inverse frame components `e_A^i`. -/
  einv : Tensor2 n
  /-- Left-to-right inverse relation `e * einv = 1`. -/
  inv_left : e * einv = 1
  /-- Right-to-left inverse relation `einv * e = 1`. -/
  inv_right : einv * e = 1

/-- Weitzenböck affine connection `Γ^k_{ij} = ∑_A e_A^k ∂_i e^A_j` constructed from the inverse
tetrad `einv A k = e_A^k` and tetrad partial derivatives `de i A j = ∂_i e^A_j`. -/
def weitzenbockConn {n : ℕ} (einv : Tensor2 n) (de : Fin n → Tensor2 n) :
    AffineConnection n :=
  fun k i j => ∑ A : Fin n, einv A k * de i A j

/-- Weitzenböck torsion tensor `T^k_{ij} = Γ^k_{ij} - Γ^k_{ji}`. -/
def weitzenbockTorsion {n : ℕ} (einv : Tensor2 n) (de : Fin n → Tensor2 n) :
    AffineConnection n :=
  torsion (weitzenbockConn einv de)

/-- Explicit tetrad-derivative formula for the Weitzenböck torsion:
`T^k_{ij} = ∑_A e_A^k (∂_i e^A_j - ∂_j e^A_i)`. -/
lemma weitzenbockTorsion_eq {n : ℕ} (einv : Tensor2 n) (de : Fin n → Tensor2 n) (k i j : Fin n) :
    weitzenbockTorsion einv de k i j = ∑ A : Fin n, einv A k * (de i A j - de j A i) := by
  simp only [weitzenbockTorsion, torsion, weitzenbockConn, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun A _ => by ring

/-- Antisymmetry of the Weitzenböck torsion in its lower indices:
`T^k_{ij} = -T^k_{ji}`. -/
lemma weitzenbockTorsion_antisymm {n : ℕ} (einv : Tensor2 n) (de : Fin n → Tensor2 n)
    (k i j : Fin n) :
    weitzenbockTorsion einv de k i j = -weitzenbockTorsion einv de k j i :=
  torsion_antisymm (weitzenbockConn einv de) k i j

/-- Covariant teleparallel superpotential
`S_{k i j} = ½ (g_{ip} T^p_{kj} - g_{jp} T^p_{ki} - g_{kp} T^p_{ij}) + g_{ki} T^m_{jm}
- g_{kj} T^m_{im}`, antisymmetric in its last two indices `(i, j)`. -/
noncomputable def superpotential (M : MetricTensor 4) (T : AffineConnection 4) :
    AffineConnection 4 :=
  fun k i j =>
    (1 / 2) *
      ((∑ p : Fin 4, M.g i p * T p k j)
        - (∑ p : Fin 4, M.g j p * T p k i)
        - (∑ p : Fin 4, M.g k p * T p i j))
      + M.g k i * torsionTrace T j
      - M.g k j * torsionTrace T i

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

/-- Quadratic teleparallel torsion scalar `T = ∑_{k,i,j} S_{k i j} T^k_{i j}` (in orthonormal or
index-raised contraction). -/
noncomputable def torsionScalar (M : MetricTensor 4) (T : AffineConnection 4) : ℝ :=
  ∑ k : Fin 4, ∑ p : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
    M.ginv k p * superpotential M T p i j *
      (∑ q : Fin 4, ∑ r : Fin 4, M.ginv i q * M.ginv j r *
        (∑ s : Fin 4, M.g k s * T s q r))

end Teleparallel

end Modified

end GeneralRelativity
