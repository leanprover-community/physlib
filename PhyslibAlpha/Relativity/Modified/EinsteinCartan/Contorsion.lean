/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Modified.EinsteinCartan.Basic
public import PhyslibAlpha.Relativity.Metrics.MetricTrace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!

# Metric compatibility and contorsion

Metric-compatible affine connections and the contorsion tensor.

## i. Overview

For a metric `g` with derivatives `dg`, every antisymmetric torsion tensor has a unique
metric-compatible connection `Γ = Γ_LC + K`, where `Γ_LC` is the Levi-Civita connection and `K`
is the contorsion tensor.

## ii. Key results

- `MetricCompatible`, `EinsteinCartanData.MetricCompatible` : metric compatibility.
- `leviCivitaOfDeriv`, `leviCivitaOfDeriv_compatible` : Levi-Civita connection from `dg`.
- `contorsion`, `contorsion_torsion`, `connection_unique` : contorsion existence and uniqueness.

## iii. Table of contents

- A. Metric compatibility and contorsion existence and uniqueness

## iv. References

* T. W. B. Kibble, *Lorentz Invariance and the Gravitational Field*, *Journal of Mathematical
  Physics* 2, pp. 212-221 (1961), Sec. 2-4. [ref: Kibble1961]
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

## A. Metric compatibility and contorsion existence and uniqueness

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


end EinsteinCartan

end Modified

end GeneralRelativity
