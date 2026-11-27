/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import PhyslibAlpha.Relativity.Metrics.MetricTrace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Einstein–Cartan–Sciama–Kibble gravitation with torsion

Affine connections with torsion, metric compatibility, explicit contorsion tensor existence and
uniqueness, Cartan's algebraic field equations in four dimensions, and recovery of General
Relativity in spinless vacuum.

## i. Overview

Einstein–Cartan theory generalizes General Relativity to Riemann–Cartan spacetimes carrying a
metric-compatible affine connection `Γ^k_{ij}` with non-vanishing torsion `T^k_{ij} = Γ^k_{ij} -
Γ^k_{ji}`. This module formalizes torsion, metric compatibility, the Levi-Civita connection from
metric derivatives, and the contorsion tensor `K^k_{ij}`, proving both existence and uniqueness of
the metric-compatible connection for any prescribed antisymmetric torsion tensor (`Γ = Γ_LC + K`).
It then defines the modified torsion tensor appearing in the Palatini variation and proves the exact
4D algebraic inversion of Cartan's spin-torsion equation (`T = κ Ŝ + …`), together with the vacuum
corollary `S = 0 → T = 0`.

## ii. Key results

- `AffineConnection`, `EinsteinCartanData`, `torsion`, `torsion_antisymm` : affine connections,
  metric-compatible connection data with torsion, and torsion tensor.
- `EinsteinCartanData.torsion`, `EinsteinCartanData.MetricCompatible`, `MetricCompatible`,
  `leviCivitaOfDeriv`, `contorsion` : metric compatibility and contorsion `K`.
- `contorsion_torsion`, `leviCivita_add_contorsion_compatible`,
  `EinsteinCartanData.connection_unique` : existence and uniqueness `Γ = Γ_LC + K` for arbitrary
  metric signature and dimension `n`.
- `modifiedTorsion`, `cartan_algebraic_inversion`, `cartan_vacuum_torsion_zero` : 4D Cartan
  algebraic spin-torsion equation inversion and spinless GR reduction.

## iii. Table of contents

- A. Affine connections and torsion tensor
- B. Metric compatibility and contorsion existence and uniqueness
- C. Cartan algebraic spin-torsion inversion in four dimensions

## iv. References

* Élie Cartan, *Sur une généralisation de la notion de courbure de Riemann et les espaces à
  torsion*, *Comptes Rendus de l'Académie des Sciences (Paris)* 174, pp. 593-595 (1922).
  [ref: Cartan1922]
* T. W. B. Kibble, *Lorentz Invariance and the Gravitational Field*, *Journal of Mathematical
  Physics* 2, pp. 212-221 (1961), Sec. 2-4. [ref: Kibble1961]
* D. W. Sciama, *The Physical Structure of General Relativity*, *Reviews of Modern Physics* 36, pp.
  463-469 (1964). [ref: Sciama1964]
* Friedrich W. Hehl et al., *General Relativity with Spin and Torsion: Foundations and Prospects*,
  *Reviews of Modern Physics* 48, pp. 393-416 (1976), Sec. II-III. [ref: Hehl1976]
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

/-!

## B. Metric compatibility and contorsion existence and uniqueness

Every metric-compatible affine connection splits uniquely into the Levi-Civita connection plus the
contorsion tensor built algebraically from its torsion.

-/

/-- Metric compatibility condition `∇_k g_{ij} = ∂_k g_{ij} - Γ^m_{ki} g_{mj} - Γ^m_{kj} g_{im}
= 0`. -/
def MetricCompatible {n : ℕ} (g : Tensor2 n) (dg : Fin n → Tensor2 n)
    (Γ : AffineConnection n) : Prop :=
  ∀ k i j : Fin n, dg k i j - (∑ m : Fin n, Γ m k i * g m j) - (∑ m : Fin n, Γ m k j * g i m) = 0

/-- Metric compatibility of an `EinsteinCartanData` geometry against metric derivatives `dg`. -/
def EinsteinCartanData.MetricCompatible {n : ℕ} (D : EinsteinCartanData n)
    (dg : Fin n → Tensor2 n) : Prop :=
  EinsteinCartan.MetricCompatible D.M.g dg D.conn

/-- Levi-Civita connection constructed from metric inverse `ginv` and metric partial derivatives
`dg k i j = ∂_k g_{ij}`. -/
noncomputable def leviCivitaOfDeriv {n : ℕ} (ginv : Tensor2 n) (dg : Fin n → Tensor2 n) :
    AffineConnection n :=
  fun k i j => (1 / 2) * ∑ m : Fin n, ginv k m * (dg j m i + dg i m j - dg m i j)

/-- Symmetry of the Levi-Civita connection in its lower indices when `dg` is symmetric. -/
lemma leviCivitaOfDeriv_symm {n : ℕ} (ginv : Tensor2 n) (dg : Fin n → Tensor2 n)
    (hdg : ∀ k i j, dg k i j = dg k j i) (k i j : Fin n) :
    leviCivitaOfDeriv ginv dg k i j = leviCivitaOfDeriv ginv dg k j i := by
  simp only [leviCivitaOfDeriv]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hdg m i j, add_comm (dg j m i) (dg i m j)]

/-- Metric compatibility of the Levi-Civita connection for any `M : MetricTensor n` and
symmetric derivative array `dg`. -/
lemma leviCivitaOfDeriv_compatible {n : ℕ} (M : MetricTensor n) (dg : Fin n → Tensor2 n)
    (hdg : ∀ k i j, dg k i j = dg k j i) :
    MetricCompatible M.g dg (leviCivitaOfDeriv M.ginv dg) := by
  intro k i j
  have hmul_l : ∀ (q : Fin n) (f : Fin n → ℝ),
      (∑ m : Fin n, ((1 / 2 : ℝ) * ∑ r : Fin n, M.ginv m r * f r) * M.g m q)
        = (1 / 2) * f q := by
    intro q f
    have hpull : (∑ m : Fin n, ((1 / 2 : ℝ) * ∑ r : Fin n, M.ginv m r * f r) * M.g m q)
        = (1 / 2) * ∑ m : Fin n, (∑ r : Fin n, M.ginv m r * f r) * M.g m q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => by ring
    rw [hpull, M.sum_mul_ginv_g_apply q f]
  have h1 := hmul_l j fun r => dg i r k + dg k r i - dg r k i
  have h2 := hmul_l i fun r => dg j r k + dg k r j - dg r k j
  have h1' : (∑ m : Fin n, leviCivitaOfDeriv M.ginv dg m k i * M.g m j)
      = (1 / 2) * (dg i j k + dg k j i - dg j k i) := h1
  have h2' : (∑ m : Fin n, leviCivitaOfDeriv M.ginv dg m k j * M.g i m)
      = (1 / 2) * (dg j i k + dg k i j - dg i k j) := by
    have hs : ∀ m, M.g i m = M.g m i := fun m => M.symm.apply m i
    simp_rw [hs]
    exact h2
  rw [h1', h2', hdg i j k, hdg k j i, hdg j k i]
  ring

/-- Contorsion tensor built from `M : MetricTensor n` and torsion `T`:
`K^k_{ij} = ½ (T^k_{ij} + g^{km} (g_{ir} T^r_{mj} + g_{jr} T^r_{mi}))`. -/
noncomputable def contorsion {n : ℕ} (M : MetricTensor n) (T : AffineConnection n) :
  AffineConnection n :=
  fun k i j => (1 / 2) * (T k i j + ∑ m : Fin n, M.ginv k m
    * (∑ r : Fin n, M.g i r * T r m j + ∑ r : Fin n, M.g j r * T r m i))

private lemma sum_contorsion_mul_g {n : ℕ} (M : MetricTensor n) (T : AffineConnection n)
    (k i j : Fin n) :
    (∑ m : Fin n, contorsion M T m k i * M.g m j)
      = (1 / 2) * ((∑ m : Fin n, M.g j m * T m k i)
        + (∑ r : Fin n, M.g k r * T r j i) + (∑ r : Fin n, M.g i r * T r j k)) := by
  simp only [contorsion]
  have hsplit : (∑ m : Fin n, (1 / 2 : ℝ) * (T m k i + ∑ p : Fin n, M.ginv m p
        * (∑ r : Fin n, M.g k r * T r p i + ∑ r : Fin n, M.g i r * T r p k)) * M.g m j)
      = (1 / 2) * ((∑ m : Fin n, T m k i * M.g m j)
        + ∑ m : Fin n, (∑ p : Fin n, M.ginv m p
          * (∑ r : Fin n, M.g k r * T r p i + ∑ r : Fin n, M.g i r * T r p k)) * M.g m j) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [hsplit, M.sum_mul_ginv_g_apply j]
  have hm : (∑ m : Fin n, T m k i * M.g m j) = ∑ m : Fin n, M.g j m * T m k i :=
    Finset.sum_congr rfl fun m _ => by rw [M.symm.apply j m]; ring
  rw [hm]
  ring

/-- Lowering the first index makes the contorsion tensor antisymmetric in its outer indices
`(m, j)` vs `(j, m)` when `T` is antisymmetric in its lower indices:
`g_{mj} K^m_{ki} + g_{im} K^m_{kj} = 0`. -/
lemma contorsion_antisymm_outer {n : ℕ} (M : MetricTensor n) (T : AffineConnection n)
    (hT : ∀ k i j, T k i j = -T k j i) (k i j : Fin n) :
    (∑ m : Fin n, contorsion M T m k i * M.g m j)
      + (∑ m : Fin n, contorsion M T m k j * M.g i m) = 0 := by
  have h1 := sum_contorsion_mul_g M T k i j
  have h2 : (∑ m : Fin n, contorsion M T m k j * M.g i m)
      = (1 / 2) * ((∑ m : Fin n, M.g i m * T m k j)
        + (∑ r : Fin n, M.g k r * T r i j) + (∑ r : Fin n, M.g j r * T r i k)) := by
    rw [Finset.sum_congr rfl fun m _ => by rw [M.symm.apply m i]]
    exact sum_contorsion_mul_g M T k j i
  rw [h1, h2]
  have ha : (∑ r : Fin n, M.g k r * T r j i) + (∑ r : Fin n, M.g k r * T r i j) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun r _ => by rw [hT r j i]; ring
  have hb : (∑ m : Fin n, M.g j m * T m k i) + (∑ r : Fin n, M.g j r * T r i k) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun r _ => by rw [hT r k i]; ring
  have hc : (∑ r : Fin n, M.g i r * T r j k) + (∑ m : Fin n, M.g i m * T m k j) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun r _ => by rw [hT r j k]; ring
  linarith

/-- Contorsion reproduces the prescribed antisymmetric torsion tensor: `torsion (contorsion M T)
= T`. -/
lemma contorsion_torsion {n : ℕ} (M : MetricTensor n) (T : AffineConnection n)
    (hT : ∀ k i j, T k i j = -T k j i) :
    torsion (contorsion M T) = T := by
  ext k i j
  simp only [torsion, contorsion]
  have h1 : ∀ m, (∑ r : Fin n, M.g i r * T r m j + ∑ r : Fin n, M.g j r * T r m i)
      - (∑ r : Fin n, M.g j r * T r m i + ∑ r : Fin n, M.g i r * T r m j) = 0 := fun m => by ring
  have hs : (∑ m : Fin n, M.ginv k m
        * (∑ r : Fin n, M.g i r * T r m j + ∑ r : Fin n, M.g j r * T r m i))
      - (∑ m : Fin n, M.ginv k m
        * (∑ r : Fin n, M.g j r * T r m i + ∑ r : Fin n, M.g i r * T r m j)) = 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun m _ => by ring
  have hT' := hT k i j
  linarith

/-- Existence of a metric-compatible connection with any prescribed antisymmetric torsion `T`:
`Γ = leviCivitaOfDeriv + contorsion`. -/
lemma leviCivita_add_contorsion_compatible {n : ℕ} (M : MetricTensor n) (dg : Fin n → Tensor2 n)
    (hdg : ∀ k i j, dg k i j = dg k j i) (T : AffineConnection n) (hT : ∀ k i j, T k i j
      = -T k j i) :
    MetricCompatible M.g dg
      (fun k i j => leviCivitaOfDeriv M.ginv dg k i j + contorsion M T k i j) := by
  intro k i j
  have hlc := leviCivitaOfDeriv_compatible M dg hdg k i j
  have hco := contorsion_antisymm_outer M T hT k i j
  simp only [add_mul, Finset.sum_add_distrib]
  linarith

/-- Torsion of `leviCivitaOfDeriv M.ginv dg + contorsion M T` equals `T`. -/
lemma leviCivita_add_contorsion_torsion {n : ℕ} (M : MetricTensor n) (dg : Fin n → Tensor2 n)
    (hdg : ∀ k i j, dg k i j = dg k j i) (T : AffineConnection n) (hT : ∀ k i j, T k i j
      = -T k j i) :
    torsion (fun k i j => leviCivitaOfDeriv M.ginv dg k i j + contorsion M T k i j) = T := by
  ext k i j
  have hsym := leviCivitaOfDeriv_symm M.ginv dg hdg k i j
  have hct := congrFun (congrFun (congrFun (contorsion_torsion M T hT) k) i) j
  simp only [torsion] at hct ⊢
  linarith

private lemma sum_g_mul_gamma_eq {n : ℕ} (M : MetricTensor n) (dg : Fin n → Tensor2 n)
    (Γ : AffineConnection n) (hmc : MetricCompatible M.g dg Γ) (k i j : Fin n) :
    2 * (∑ m : Fin n, M.g k m * Γ m i j)
      = (dg j k i + dg i k j - dg k i j)
        + (∑ m : Fin n, M.g k m * torsion Γ m i j)
        + (∑ m : Fin n, M.g i m * torsion Γ m k j)
        + (∑ m : Fin n, M.g j m * torsion Γ m k i) := by
  have h1 := hmc j k i
  have h2 := hmc i k j
  have h3 := hmc k i j
  have hs : ∀ a b c : Fin n, (∑ m : Fin n, Γ m a b * M.g m c)
      = ∑ m : Fin n, M.g c m * Γ m a b := fun a b c =>
    Finset.sum_congr rfl fun m _ => by rw [M.symm.apply c m]; ring
  have hs' : ∀ a b c : Fin n, (∑ m : Fin n, Γ m a b * M.g c m)
      = ∑ m : Fin n, M.g c m * Γ m a b := fun a b c =>
    Finset.sum_congr rfl fun m _ => by ring
  rw [hs j k i, hs' j i k] at h1
  rw [hs i k j, hs' i j k] at h2
  rw [hs k i j, hs' k j i] at h3
  have ht : ∀ a b c : Fin n, (∑ m : Fin n, M.g a m * torsion Γ m b c)
      = (∑ m : Fin n, M.g a m * Γ m b c) - (∑ m : Fin n, M.g a m * Γ m c b) := fun a b c => by
    simp only [torsion, mul_sub, Finset.sum_sub_distrib]
  rw [ht k i j, ht i k j, ht j k i]
  linarith

/-- Uniqueness of a metric-compatible connection: every metric-compatible connection `Γ` equals
`leviCivitaOfDeriv M.ginv dg + contorsion M (torsion Γ)`. -/
lemma connection_unique {n : ℕ} (M : MetricTensor n) (dg : Fin n → Tensor2 n)
    (Γ : AffineConnection n) (hmc : MetricCompatible M.g dg Γ) :
    Γ = fun k i j => leviCivitaOfDeriv M.ginv dg k i j + contorsion M (torsion Γ) k i j := by
  ext p i j
  have hcontract := M.sum_ginv_mul_g_apply p
  have hsum : ∑ k : Fin n, M.ginv p k * (2 * (∑ m : Fin n, M.g k m * Γ m i j))
      = 2 * Γ p i j := by
    have hmul : (∑ k : Fin n, M.ginv p k * (2 * (∑ m : Fin n, M.g k m * Γ m i j)))
        = 2 * ∑ k : Fin n, M.ginv p k * (∑ m : Fin n, M.g k m * Γ m i j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hmul, hcontract (fun k => Γ k i j)]
  have hdiv := congrArg (fun x => (1 / 2 : ℝ) * x) hsum
  have hrhs : ∑ k : Fin n, M.ginv p k * (2 * (∑ m : Fin n, M.g k m * Γ m i j))
      = ∑ k : Fin n, M.ginv p k * ((dg j k i + dg i k j - dg k i j)
        + (∑ m : Fin n, M.g k m * torsion Γ m i j)
        + (∑ m : Fin n, M.g i m * torsion Γ m k j)
        + (∑ m : Fin n, M.g j m * torsion Γ m k i)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_g_mul_gamma_eq M dg Γ hmc k i j]
  rw [hrhs] at hdiv
  have hsplit : (∑ k : Fin n, M.ginv p k * ((dg j k i + dg i k j - dg k i j)
        + (∑ m : Fin n, M.g k m * torsion Γ m i j)
        + (∑ m : Fin n, M.g i m * torsion Γ m k j)
        + (∑ m : Fin n, M.g j m * torsion Γ m k i)))
      = (∑ k : Fin n, M.ginv p k * (dg j k i + dg i k j - dg k i j))
        + (∑ k : Fin n, M.ginv p k * (∑ m : Fin n, M.g k m * torsion Γ m i j))
        + (∑ k : Fin n, M.ginv p k
          * (∑ r : Fin n, M.g i r * torsion Γ r k j + ∑ r : Fin n, M.g j r * torsion Γ r k i)) := by
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  rw [hsplit, M.sum_ginv_mul_g_apply p (fun k => torsion Γ k i j)] at hdiv
  simp only [leviCivitaOfDeriv, contorsion]
  linarith

/-- Uniqueness of metric-compatible connections packaged on `EinsteinCartanData`:
`D.conn = leviCivitaOfDeriv D.M.ginv dg + contorsion D.M D.torsion`. -/
lemma EinsteinCartanData.connection_unique {n : ℕ} (D : EinsteinCartanData n)
    (dg : Fin n → Tensor2 n) (hmc : D.MetricCompatible dg) :
    D.conn = fun k i j =>
      leviCivitaOfDeriv D.M.ginv dg k i j + contorsion D.M D.torsion k i j :=
  EinsteinCartan.connection_unique D.M dg D.conn hmc

/-!

## C. Cartan algebraic spin-torsion inversion in four dimensions

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

/-- Algebraic inverse helper for `modifiedTorsion`: recovers torsion `T` from the Palatini source
`S = κ Σ` in 4D via `T^k_{ij} = S^k_{ij} + ½ (δ^k_i S^m_{jm} - δ^k_j S^m_{im})`, needed to
isolate the algebraic inversion of Cartan's spin-torsion field equation cleanly. -/
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
