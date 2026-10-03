/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.Basic
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.Bidual
public import PhyslibAlpha.ProbabilisticTheory.Classical.NamiokaPhelps
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Classical systems are nuclear

Namioka–Phelps: a system is classical exactly when it is nuclear.

## i. Overview

A classical system composes uniquely with every other system: every composite observable in the
maximal cone is, up to an arbitrarily small multiple of the unit, a sum of products of nonnegative
observables. Together with the converse, a system is classical exactly when it is nuclear. This is
the theorem of Namioka and Phelps.

The proof measures and prepares. In the bidual of a classical system, finitely many observables are
close to step functions on a partition of the unit. Each piece of the partition is detected by a
state of the system. Measuring with these states and preparing the pieces approximates the
observables, and applied to a composite observable in the maximal cone it produces nonnegative
products. A positive functional on the minimal cone therefore cannot separate a maximal-cone
observable from the minimal cone.

## ii. Key results

- `Bidual.hasMonotoneSups` : increasing sequences in the bidual have least upper bounds.
- `Bidual.exists_apply_ge` : every nonzero piece of the unit is detected by a state.
- `Bidual.exists_measure_prepare` : finitely many elements of the bidual of a classical system are
  approximated by measuring with states and preparing pieces of the unit.
- `Nuclear.apply_nonneg_of_mem_maxTensorCone` : for a classical system, a functional nonnegative on
  the minimal cone is nonnegative on the maximal cone.
- `IsClassical.isNuclear` : classical systems are nuclear.
- `isClassical_iff_isNuclear` : **Namioka–Phelps**: a system is classical exactly when it is
  nuclear.

## iii. Table of contents

- A. Monotone suprema and detection
- B. Measure and prepare
- C. Positive functionals on the minimal cone
- D. Positive functionals on the minimal cone are positive on the maximal cone
- E. Classical systems are nuclear

## iv. References

- I. Namioka and R. R. Phelps, *Tensor products of compact convex sets*, Pacific J. Math. 31 (1969),
  469–480.

-/

@[expose] public section


namespace Bidual
open ProbabilisticTheory
open OrderUnitLattice VectorLattice

variable {E : Type*} [OrderUnitSpace E]

/-! ## A. Monotone suprema and detection -/

variable [hE : Fact (HasLatticeDualCone E)]

/-- Increasing sequences below the unit have least upper bounds in the bidual. -/
lemma hasMonotoneSups : HasMonotoneSups (1 : Bidual E) := fun _ ha hb =>
  ⟨ciSup ha.directed_le hb, isLUB_ciSup ha.directed_le hb⟩

/-- **Detection.** A nonzero piece of the unit that is disjoint from its complement is detected by
a state: some state assigns it probability close to `1`. -/
lemma exists_apply_ge {c : Bidual E} (hc0 : 0 ≤ c) (hc : c ⊓ (1 - c) = 0) (hne : c ≠ 0) {θ : ℝ}
    (hθ : 0 < θ) : ∃ φ : E →ₚ[ℝ] ℝ, φ 1 = 1 ∧ 1 - θ ≤ c φ := by
  by_contra! h
  refine hne (eq_zero_of_le_smul OrderUnitSpace.one_nonneg hc0 hc (by linarith : 1 - θ < 1)
    fun ψ => ?_)
  show c ψ ≤ (1 - θ) * ψ 1
  rcases (map_nonneg ψ OrderUnitSpace.one_nonneg).eq_or_lt with h0 | hpos
  · rw [PositiveLinearMap.eq_zero_of_map_one_eq_zero h0.symm, c.map_zero]
    simp
  · have hφ : ((ψ 1)⁻¹.toNNReal • ψ) 1 = 1 := by
      simp [Real.coe_toNNReal _ (inv_nonneg.2 hpos.le), inv_mul_cancel₀ hpos.ne']
    have := h _ hφ
    rw [c.map_nnsmul, Real.coe_toNNReal _ (inv_nonneg.2 hpos.le), inv_mul_lt_iff₀ hpos] at this
    linarith

/-! ## B. Measure and prepare -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → Bidual E}

omit [DecidableEq ι] in
/-- Every nonzero piece of a partition is detected by a state. -/
lemma exists_detecting (hs : IsPartition 1 s) {θ : ℝ} (hθ : 0 < θ) :
    ∃ φ : ι → E →ₚ[ℝ] ℝ, ∀ i, s i ≠ 0 → φ i 1 = 1 ∧ 1 - θ ≤ s i (φ i) := by
  classical
  have h (i : ι) (hi : s i ≠ 0) := exists_apply_ge (hs.1 i) (hs.inf_sub i) hi hθ
  exact ⟨fun i => if hi : s i = 0 then 0 else (h i hi).choose, fun i hi => by
    simpa [hi] using (h i hi).choose_spec⟩

omit hE [DecidableEq ι] in
/-- Evaluating a step function at a state. -/
lemma sum_smul_apply (c : ι → ℝ) (φ : E →ₚ[ℝ] ℝ) :
    (∑ i, c i • s i) φ = ∑ i, c i * s i φ := by
  rw [← eval_apply, _root_.map_sum]; rfl

omit hE [DecidableEq ι] in
lemma sum_apply' (φ : E →ₚ[ℝ] ℝ) : (∑ i, s i) φ = ∑ i, s i φ := by
  rw [← eval_apply, _root_.map_sum]; rfl

/-- If `x` lies between two step functions on a partition, a state that detects the piece `s i`
sees `x` between the two levels on that piece, up to `2 * A * θ`. -/
lemma apply_mem_of_detect (hs : IsPartition 1 s) {x : Bidual E} {a b : ι → ℝ}
    (hlo : ∑ i, a i • s i ≤ x) (hhi : x ≤ ∑ i, b i • s i) {φ : E →ₚ[ℝ] ℝ} (hφ : φ 1 = 1)
    {i : ι} {θ A : ℝ} (hφi : 1 - θ ≤ s i φ) (ha : ∀ l, |a l| ≤ A) (hb : ∀ l, |b l| ≤ A) :
    a i - 2 * A * θ ≤ x φ ∧ x φ ≤ b i + 2 * A * θ := by
  have hq1 : ∑ l, s l φ = 1 := by
    rw [← sum_apply', hs.2.2, coe_one, hφ]
  have h₁ := abs_le.1 (Real.abs_sum_mul_sub_le (fun l => hs.1 l φ) hq1 i hφi ha)
  have h₂ := abs_le.1 (Real.abs_sum_mul_sub_le (fun l => hs.1 l φ) hq1 i hφi hb)
  have e₁ : (∑ i, a i • s i) φ ≤ x φ := hlo φ
  have e₂ : x φ ≤ (∑ i, b i • s i) φ := hhi φ
  rw [sum_smul_apply] at e₁ e₂
  beta_reduce at h₁ h₂
  exact ⟨by linarith, by linarith⟩

omit hE in
/-- A common bound for finitely many levels and their shifts. -/
lemma exists_levels_bound {m n : ℕ} (a : Fin m → Fin n → ℝ) (c : ℝ) :
    ∃ A, 0 ≤ A ∧ ∀ i k, |a i k| ≤ A ∧ |a i k + c| ≤ A := by
  refine ⟨∑ i, ∑ k, |a i k| + |c|, add_nonneg (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _), fun i k => ?_⟩
  have h₁ : |a i k| ≤ ∑ i, ∑ k, |a i k| :=
    (Finset.single_le_sum (fun k _ => abs_nonneg (a i k)) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i => ∑ k, |a i k|)
        (fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _) (Finset.mem_univ i))
  exact ⟨by linarith [abs_nonneg c], (abs_add_le _ _).trans (by linarith)⟩

omit hE in
/-- A detection error `θ` small enough that `2 * A * θ ≤ η / 4`. -/
lemma exists_error_param {η A : ℝ} (hη : 0 < η) (hA : 0 ≤ A) :
    ∃ θ, 0 < θ ∧ 2 * A * θ ≤ η / 4 := by
  refine ⟨η / 2 / (4 * A + 1), by positivity, ?_⟩
  have : η / 2 / (4 * A + 1) * (4 * A + 1) = η / 2 := div_mul_cancel₀ _ (by positivity)
  nlinarith [show 0 < η / 2 / (4 * A + 1) by positivity]

/-- **Measure and prepare.** In the bidual of a classical system, finitely many elements are
uniformly close to the result of measuring them with finitely many states `φ i` and preparing the
pieces `p i` of a partition of the unit. -/
lemma exists_measure_prepare {n : ℕ} (x : Fin n → Bidual E) {η : ℝ} (hη : 0 < η) :
    ∃ (m : ℕ) (p : Fin m → Bidual E) (φ : Fin m → E →ₚ[ℝ] ℝ), IsPartition 1 p ∧
      ∀ k, x k - ∑ i, x k (φ i) • p i ≤ η • 1 ∧ -(η • 1) ≤ x k - ∑ i, x k (φ i) • p i := by
  obtain ⟨m, p, a, hp, hloc⟩ := exists_partition_approx hasMonotoneSups
    OrderUnitSpace.one_nonneg OrderUnitSpace.isOrderUnit_one.isStrongUnit x (half_pos hη)
  obtain ⟨A, hA0, hA⟩ := exists_levels_bound a (η / 2)
  obtain ⟨θ, hθ, h2⟩ := exists_error_param hη hA0
  obtain ⟨φ, hφ⟩ := exists_detecting hp hθ
  refine ⟨m, p, φ, hp, fun k => ?_⟩
  have hunit := (OrderUnitSpace.isOrderUnit_one (E := Bidual E)).isStrongUnit
  have hlo := hp.sum_le hunit (a := fun i => a i k) fun i => (hloc i k).2
  have hhi := hp.le_sum hunit (b := fun i => a i k + η / 2) fun i => (hloc i k).1
  have hnear (i : Fin m) (hi : p i ≠ 0) := apply_mem_of_detect hp hlo hhi (hφ i hi).1 (hφ i hi).2
    (fun l => (hA l k).1) fun l => (hA l k).2
  constructor
  · calc x k - ∑ i, x k (φ i) • p i ≤ ∑ i, (a i k + η / 2) • p i - ∑ i, x k (φ i) • p i :=
          sub_le_sub_right hhi _
      _ = ∑ i, (a i k + η / 2 - x k (φ i)) • p i := by
          rw [← Finset.sum_sub_distrib]; simp only [sub_smul]
      _ ≤ η • 1 := hp.sum_smul_le fun i hi => by linarith [(hnear i hi).1]
  · calc -(η • (1 : Bidual E)) = (-η) • 1 := (neg_smul _ _).symm
      _ ≤ ∑ i, (a i k - x k (φ i)) • p i := hp.le_sum_smul fun i hi => by
          linarith [(hnear i hi).2]
      _ = ∑ i, a i k • p i - ∑ i, x k (φ i) • p i := by
          rw [← Finset.sum_sub_distrib]; simp only [sub_smul]
      _ ≤ x k - ∑ i, x k (φ i) • p i := sub_le_sub_right hlo _

end Bidual

namespace ProbabilisticTheory

open OrderUnitLattice VectorLattice

/-! ## C. Positive functionals on the minimal cone -/

namespace Nuclear

open TensorProduct PositiveLinearMap

variable {E F : Type*} [OrderUnitSpace E] [OrderUnitSpace F]
  {Λ : E ⊗[ℝ] F →ₗ[ℝ] ℝ} (hΛ : ∀ w ∈ minTensorCone E F, 0 ≤ Λ w)
include hΛ

/-- The positive functional `x ↦ Λ (x ⊗ y)` on `E`, for `y ≥ 0`. -/
def slice (y : F) (hy : 0 ≤ y) : E →ₚ[ℝ] ℝ :=
  .mk₀ (Λ ∘ₗ (TensorProduct.mk ℝ E F).flip y) fun _ hx => hΛ _ (tmul_mem_minTensorCone hx hy)

@[simp] lemma slice_apply (y : F) (hy : 0 ≤ y) (x : E) : slice hΛ y hy x = Λ (x ⊗ₜ[ℝ] y) := rfl

lemma slice_add {y y' : F} (hy : 0 ≤ y) (hy' : 0 ≤ y') :
    slice hΛ (y + y') (add_nonneg hy hy') = slice hΛ y hy + slice hΛ y' hy' :=
  PositiveLinearMap.ext fun x => by simp [tmul_add]

lemma slice_smul {c : ℝ} (hc : 0 ≤ c) {y : F} (hy : 0 ≤ y) :
    slice hΛ (c • y) (smul_nonneg hc hy) = c.toNNReal • slice hΛ y hy :=
  PositiveLinearMap.ext fun x => by simp [tmul_smul, Real.coe_toNNReal _ hc]

/-- A nonnegative element of the bidual of `E`, paired with `F` through `Λ`: a positive functional
on `F` with value `p (x ↦ Λ (x ⊗ y))` at `y ≥ 0`. -/
noncomputable def pairing {p : Bidual E} (hp : 0 ≤ p) : F →ₚ[ℝ] ℝ := by
  classical
  exact ofCone (fun y => if hy : 0 ≤ y then p (slice hΛ y hy) else 0)
    (fun y hy => by simp only [hy, ↓reduceDIte]; exact hp _)
    (fun y y' hy hy' => by
      simp only [hy, hy', add_nonneg hy hy', ↓reduceDIte, slice_add, p.map_add])
    (fun c y hc hy => by
      simp only [hy, smul_nonneg hc.le hy, ↓reduceDIte, slice_smul hΛ hc.le hy,
        p.map_nnsmul, Real.coe_toNNReal _ hc.le])

lemma pairing_apply {p : Bidual E} (hp : 0 ≤ p) {y : F} (hy : 0 ≤ y) :
    pairing hΛ hp y = p (slice hΛ y hy) := by
  classical
  rw [pairing, ofCone_apply _ _ _ _ hy]
  simp [hy]

/-- If an observable of `E` is a combination of nonnegative elements `p i` of the bidual plus a
remainder `d`, then `Λ (e ⊗ f)` is the corresponding combination of pairings plus the remainder
evaluated on two slices. -/
lemma apply_tmul_eq {ι : Type*} [Fintype ι] {e : E} {p : ι → Bidual E} (hp : ∀ i, 0 ≤ p i)
    (c : ι → ℝ) {d : Bidual E} (he : Bidual.ofE e = ∑ i, c i • p i + d) (f : F) {N : ℝ}
    (hN : 0 ≤ f + N • 1) (hN0 : 0 ≤ N) :
    Λ (e ⊗ₜ[ℝ] f) = ∑ i, c i * pairing hΛ (hp i) f +
      (d (slice hΛ _ hN) - d (slice hΛ _ (smul_nonneg hN0 OrderUnitSpace.one_nonneg))) := by
  have hB := smul_nonneg hN0 (OrderUnitSpace.one_nonneg (E := F))
  have hval (y : F) (hy : 0 ≤ y) :
      Λ (e ⊗ₜ[ℝ] y) = ∑ i, c i * p i (slice hΛ y hy) + d (slice hΛ y hy) := by
    rw [← slice_apply hΛ y hy, ← Bidual.ofE_apply, he, Bidual.coe_add, Bidual.sum_smul_apply]
  have hpair (i : ι) : pairing hΛ (hp i) f =
      p i (slice hΛ _ hN) - p i (slice hΛ _ hB) := by
    rw [← pairing_apply hΛ (hp i) hN, ← pairing_apply hΛ (hp i) hB, ← map_sub, add_sub_cancel_right]
  have hsplit : Λ (e ⊗ₜ[ℝ] f) = Λ (e ⊗ₜ[ℝ] (f + N • 1)) - Λ (e ⊗ₜ[ℝ] (N • (1 : F))) := by
    rw [← map_sub, ← tmul_sub, add_sub_cancel_right]
  rw [hsplit, hval _ hN, hval _ hB]
  simp only [hpair, mul_sub, Finset.sum_sub_distrib]
  ring

end Nuclear

/-! ## D. Positive functionals on the minimal cone are positive on the maximal cone -/

namespace Nuclear

open TensorProduct PositiveLinearMap

variable {E F : Type*} [OrderUnitSpace E] [Fact (HasLatticeDualCone E)]
  [ArchimedeanOrderUnitSpace F] {Λ : E ⊗[ℝ] F →ₗ[ℝ] ℝ} (hΛ : ∀ w ∈ minTensorCone E F, 0 ≤ Λ w)

omit [Fact (HasLatticeDualCone E)] in
/-- Measuring the first factor of a maximal-cone observable with a positive functional leaves a
nonnegative observable. -/
lemma lslice_nonneg {z : E ⊗[ℝ] F} (hz : z ∈ maxTensorCone E F) (φ : E →ₚ[ℝ] ℝ) :
    0 ≤ lslice φ z :=
  (UnitalPositiveLinearMap.nonneg_iff_forall_state_nonneg _).2 fun ω => by
    have := mem_maxTensorCone.1 hz φ ω.toPositiveLinearMap
    rwa [tensor_apply_eq_lslice] at this

include hΛ

omit [Fact (HasLatticeDualCone E)] in
/-- The measured-and-prepared part of `Λ z` is nonnegative. -/
lemma sum_pairing_nonneg {n m : ℕ} {e : Fin n → E} {f : Fin n → F} {p : Fin m → Bidual E}
    (hp : ∀ i, 0 ≤ p i) (φ : Fin m → E →ₚ[ℝ] ℝ)
    (hz : ∑ k, e k ⊗ₜ[ℝ] f k ∈ maxTensorCone E F) :
    0 ≤ ∑ k, ∑ i, Bidual.ofE (e k) (φ i) * pairing hΛ (hp i) (f k) := by
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun i _ => ?_
  have : ∑ k, Bidual.ofE (e k) (φ i) * pairing hΛ (hp i) (f k) =
      pairing hΛ (hp i) (lslice (φ i) (∑ k, e k ⊗ₜ[ℝ] f k)) := by
    simp only [_root_.map_sum, lslice_tmul, map_smul, smul_eq_mul, Bidual.ofE_apply]
  rw [this]
  exact map_nonneg _ (lslice_nonneg hz (φ i))

omit [Fact (HasLatticeDualCone E)] hΛ in
/-- A remainder within `η • 1` changes an evaluation on nonnegative functionals by at most `η`
times their weight. -/
lemma remainder_bound {d : Bidual E} {η : ℝ} (h₁ : d ≤ η • 1) (h₂ : -(η • 1) ≤ d)
    (ψ₁ ψ₂ : E →ₚ[ℝ] ℝ) : -(η * (ψ₁ 1 + ψ₂ 1)) ≤ d ψ₁ - d ψ₂ := by
  have e₁ := h₂ ψ₁
  have e₂ := h₁ ψ₂
  simp only [Bidual.coe_neg, Bidual.coe_smul, Bidual.coe_one] at e₁ e₂
  linarith

/-- **Positive on the minimal cone, positive on the maximal cone.** For a classical system `E`, a
functional on `E ⊗ F` that is nonnegative on sums of products of nonnegative observables is
nonnegative on the whole maximal cone. -/
lemma apply_nonneg_of_mem_maxTensorCone {z : E ⊗[ℝ] F} (hz : z ∈ maxTensorCone E F) :
    0 ≤ Λ z := by
  obtain ⟨n, e, f, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  choose N hN using fun k => OrderUnitSpace.exists_nsmul_one_le (-f k)
  have hN' (k : Fin n) : 0 ≤ f k + (N k : ℝ) • 1 := by
    rw [Nat.cast_smul_eq_nsmul]; exact neg_le_iff_add_nonneg'.1 (hN k)
  have hB (k : Fin n) : (0 : F) ≤ (N k : ℝ) • 1 :=
    smul_nonneg (N k).cast_nonneg OrderUnitSpace.one_nonneg
  set C := ∑ k, (slice hΛ _ (hN' k) 1 + slice hΛ _ (hB k) 1)
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ =>
    add_nonneg (map_nonneg _ OrderUnitSpace.one_nonneg) (map_nonneg _ OrderUnitSpace.one_nonneg)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨m, p, φ, hp, hd⟩ := Bidual.exists_measure_prepare (fun k => Bidual.ofE (e k))
    (div_pos hε (by linarith : (0 : ℝ) < C + 1))
  have hterm (k : Fin n) := apply_tmul_eq hΛ hp.1 (fun i => Bidual.ofE (e k) (φ i))
    (d := Bidual.ofE (e k) - ∑ i, Bidual.ofE (e k) (φ i) • p i) (by abel) (f k) (hN' k)
    (N k).cast_nonneg
  have herr (k : Fin n) := remainder_bound (hd k).1 (hd k).2 (slice hΛ _ (hN' k))
    (slice hΛ _ (hB k))
  have hmain := sum_pairing_nonneg hΛ hp.1 φ hz
  rw [_root_.map_sum, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => herr k
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
  have hηC : ε / (C + 1) * C ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  linarith

end Nuclear

/-! ## E. Classical systems are nuclear -/

section Final

open TensorProduct PositiveLinearMap

variable {E F : Type*} [ArchimedeanOrderUnitSpace E] [ArchimedeanOrderUnitSpace F]

lemma eq_zero_of_subsingleton_left [Subsingleton E] (w : E ⊗[ℝ] F) : w = 0 := by
  obtain ⟨n, e, f, rfl⟩ := TensorProduct.exists_sum_tmul_eq w
  simp [Subsingleton.elim (e _) 0]

lemma eq_zero_of_subsingleton_right [Subsingleton F] (w : E ⊗[ℝ] F) : w = 0 := by
  obtain ⟨n, e, f, rfl⟩ := TensorProduct.exists_sum_tmul_eq w
  simp [Subsingleton.elim (f _) 0]

/-- **Classical systems are nuclear (Namioka–Phelps).** If the positive functionals on `E` form a
lattice, then composing `E` with any Archimedean system `F` is unique: every composite observable in
the maximal cone lies in the closure of the minimal cone. -/
lemma IsClassical.isNuclear (hE : IsClassical E) : IsNuclear E := by
  intro F _ z hz ε hε
  have : Fact (HasLatticeDualCone E) := ⟨hE⟩
  rcases subsingleton_or_nontrivial E with _ | _
  · rw [eq_zero_of_subsingleton_left (z + _)]; exact zero_mem _
  rcases subsingleton_or_nontrivial F with _ | _
  · rw [eq_zero_of_subsingleton_right (z + _)]; exact zero_mem _
  obtain ⟨ω⟩ := UnitalPositiveLinearMap.instNonemptyState (E := E)
  obtain ⟨ω'⟩ := UnitalPositiveLinearMap.instNonemptyState (E := F)
  by_contra hne
  obtain ⟨Λ, hΛ, hΛz⟩ := isDominatedCone_minTensorCone.exists_apply_neg
    (Λ₀ := tensor ω.toPositiveLinearMap ω'.toPositiveLinearMap)
    (fun c hc => mem_maxTensorCone.1 (minTensorCone_le_maxTensorCone hc) _ _)
    (by rw [tensor_tmul]; exact (show ω 1 * ω' 1 = 1 by simp).symm ▸ one_pos) hε hne
  exact absurd (Nuclear.apply_nonneg_of_mem_maxTensorCone hΛ hz) (not_le.2 hΛz)

/-- **Namioka–Phelps.** An Archimedean order-unit space is classical — its positive functionals
form a lattice, its state space is a Choquet simplex — exactly when it is nuclear: it composes
uniquely with every other Archimedean system. -/
lemma isClassical_iff_isNuclear : IsClassical E ↔ IsNuclear E :=
  ⟨IsClassical.isNuclear, IsNuclear.isClassical⟩

end Final

end ProbabilisticTheory
