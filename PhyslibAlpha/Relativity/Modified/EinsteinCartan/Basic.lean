/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import PhyslibAlpha.Relativity.Metrics.MetricTrace
import Mathlib.Tactic.Ring
/-!

# Einstein–Cartan connections and torsion

Affine connections, Einstein–Cartan data, and the torsion tensor.

## i. Overview

An affine connection `Γ^k_{ij}` carries torsion `T^k_{ij} = Γ^k_{ij} - Γ^k_{ji}`. This module
defines connections, metric-compatible connection data, the torsion tensor, and its basic
antisymmetry and vanishing properties.

## ii. Key results

- `AffineConnection`, `EinsteinCartanData` : affine connections and Einstein–Cartan data.
- `torsion`, `EinsteinCartanData.torsion` : torsion of a connection.
- `torsion_antisymm`, `torsion_diag`, `torsion_eq_zero_of_symm` : torsion API.

## iii. Table of contents

- A. Affine connections and torsion tensor

## iv. References

* Élie Cartan, *Sur une généralisation de la notion de courbure de Riemann et les espaces à
  torsion*, *Comptes Rendus de l'Académie des Sciences (Paris)* 174, pp. 593-595 (1922).
  [ref: Cartan1922]
* T. W. B. Kibble, *Lorentz Invariance and the Gravitational Field*, *Journal of Mathematical
  Physics* 2, pp. 212-221 (1961), Sec. 2-4. [ref: Kibble1961]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace EinsteinCartan

/-!

## A. Affine connections and torsion tensor

Relaxing connection symmetry replaces zero torsion by the antisymmetric Cartan tensor
`T^k_{ij} = Γ^k_{ij} - Γ^k_{ji}`, which vanishes identically for Levi-Civita connections.

-/

/-- General `(1,2)` affine connection coefficients `Γ^k_{ij}` in `n` dimensions. -/
abbrev AffineConnection (n : ℕ) : Type := Fin n → Fin n → Fin n → ℝ

/-- Riemann–Cartan spacetime data in `n` dimensions pairing a nondegenerate metric with a
(generally torsionful) affine connection. -/
structure EinsteinCartanData (n : ℕ) where
  /-- Nondegenerate spacetime metric tensor. -/
  M : MetricTensor n
  /-- General `(1,2)` affine connection coefficients `Γ^k_{ij}`. -/
  conn : AffineConnection n

/-- Cartan torsion tensor `T^k_{ij} = Γ^k_{ij} - Γ^k_{ji}`. -/
def torsion {n : ℕ} (Γ : AffineConnection n) : AffineConnection n :=
  fun k i j => Γ k i j - Γ k j i

/-- Torsion tensor of the affine connection carried by an `EinsteinCartanData`. -/
def EinsteinCartanData.torsion {n : ℕ} (D : EinsteinCartanData n) : AffineConnection n :=
  EinsteinCartan.torsion D.conn

/-- Antisymmetry of torsion in its lower two indices: `T^k_{ij} = -T^k_{ji}`. -/
lemma torsion_antisymm {n : ℕ} (Γ : AffineConnection n) (k i j : Fin n) :
    torsion Γ k i j = -torsion Γ k j i := by
  simp only [torsion]
  ring

/-- Vanishing diagonal components of torsion: `T^k_{ii} = 0`. -/
lemma torsion_diag {n : ℕ} (Γ : AffineConnection n) (k i : Fin n) : torsion Γ k i i = 0 := by
  simp [torsion]

/-- Antisymmetry of the torsion of an `EinsteinCartanData` in its lower two indices. -/
lemma EinsteinCartanData.torsion_antisymm {n : ℕ} (D : EinsteinCartanData n) (k i j : Fin n) :
    D.torsion k i j = -D.torsion k j i :=
  GeneralRelativity.Modified.EinsteinCartan.torsion_antisymm D.conn k i j

/-- Diagonal components of the torsion of an `EinsteinCartanData` vanish. -/
lemma EinsteinCartanData.torsion_diag {n : ℕ} (D : EinsteinCartanData n) (k i : Fin n) :
    D.torsion k i i = 0 :=
  GeneralRelativity.Modified.EinsteinCartan.torsion_diag D.conn k i

/-- Any symmetric connection (such as Levi-Civita) has zero torsion. -/
lemma torsion_eq_zero_of_symm {n : ℕ} (Γ : AffineConnection n) (hs : ∀ k i j, Γ k i j = Γ k j i) :
    torsion Γ = 0 := by
  ext k i j
  simp [torsion, hs k i j]

/-- Adding a symmetric `(1,2)` tensor leaves torsion unchanged. -/
lemma torsion_add_symm {n : ℕ} (Γ S : AffineConnection n) (hs : ∀ k i j, S k i j = S k j i) :
    torsion (fun k i j => Γ k i j + S k i j) = torsion Γ := by
  ext k i j
  simp only [torsion, hs k i j]
  ring


end EinsteinCartan

end Modified

end GeneralRelativity
