/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Order.PositiveDual.Interpolation
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.PositiveDual
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Interpolation of complete observables

## i. Overview

Given finitely many lower observables `a i` below finitely many upper observables `b j`, an
interpolant is an observable `g` with `a i ≤ g ≤ b j` for all `i` and `j`. When the positive
functionals form a lattice, interpolants exist up to any error `ε • 1`. When the observables are
moreover complete in the order-unit norm, interpolants with errors `(1 / 2) ^ k` converge, and
exact interpolants exist. Then the observables have the Riesz decomposition.

## ii. Key results

- `HasLatticeDualCone.exists_interpolant` : on a complete Archimedean order-unit space, exact
  interpolants exist.
- `HasLatticeDualCone.hasRieszDecomposition` : on a complete Archimedean order-unit space,
  observables then have the Riesz decomposition.

## iii. Table of contents

- A. Closed order intervals
- B. Exact interpolants

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. Closed order intervals -/

namespace ArchimedeanOrderUnitSpace

open scoped ArchimedeanOrderUnitSpace

variable {F : Type*} [ArchimedeanOrderUnitSpace F]

lemma isClosed_setOf_le (c : F) : IsClosed {x : F | c ≤ x} := by
  rw [show {x : F | c ≤ x} = (fun x => x - c) ⁻¹' Set.Ici 0 by ext; simp]
  exact isClosed_Ici.preimage (continuous_id.sub continuous_const)

lemma isClosed_setOf_ge (c : F) : IsClosed {x : F | x ≤ c} := by
  rw [show {x : F | x ≤ c} = (fun x => c - x) ⁻¹' Set.Ici 0 by ext; simp]
  exact isClosed_Ici.preimage (continuous_const.sub continuous_id)

/-- Two observables within `c • 1` of each other are at distance at most `c`. -/
lemma dist_le_of_le_of_le {x y : F} {c : ℝ} (hc : 0 ≤ c) (h₁ : x - c • 1 ≤ y)
    (h₂ : y ≤ x + c • 1) : dist x y ≤ c := by
  rw [dist_eq_norm]
  exact orderUnitNorm_le_iff.2 ⟨hc, by rw [neg_le_sub_iff_le_add]; exact h₂,
    by rw [sub_le_comm]; exact h₁⟩

/-- An observable below every power `(1 / 2) ^ k` of the unit is nonpositive. -/
lemma le_zero_of_forall_le_half_pow {x : F} (hx : ∀ k : ℕ, x ≤ ((1 / 2 : ℝ) ^ k) • 1) : x ≤ 0 :=
  le_zero_of_forall_pos_smul_one_le x fun ε hε => by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    exact (hx k).trans (smul_le_smul_of_nonneg_right hk.le OrderUnitSpace.one_nonneg)

end ArchimedeanOrderUnitSpace

/-! ## B. Exact interpolants -/

end ProbabilisticTheory

namespace HasLatticeDualCone
open ProbabilisticTheory

open scoped ArchimedeanOrderUnitSpace
open Filter Topology ArchimedeanOrderUnitSpace

variable {F : Type*} [ArchimedeanOrderUnitSpace F] (hF : HasLatticeDualCone F) {n m : ℕ}
  {a : Fin n → F} {b : Fin m → F} (hab : ∀ i j, a i ≤ b j)
include hF hab

omit hF hab in
/-- `g` interpolates between `a` and `b` up to `δ`. -/
def IsApproxInterpolant (a : Fin n → F) (b : Fin m → F) (δ : ℝ) (g : F) : Prop :=
  (∀ i, a i ≤ g + δ • 1) ∧ ∀ j, g ≤ b j + δ • 1

omit hF in
/-- Appending `g - δ • 1` below and `g + δ • 1` above keeps the lower observables below the upper
ones. -/
lemma snoc_le_snoc {δ : ℝ} (hδ : 0 ≤ δ) {g : F} (hg : IsApproxInterpolant a b δ g) (i : Fin (n + 1))
    (j : Fin (m + 1)) : Fin.snoc (α := fun _ => F) a (g - δ • 1) i ≤
      Fin.snoc (α := fun _ => F) b (g + δ • 1) j := by
  have hδ1 : (0 : F) ≤ δ • 1 := smul_nonneg hδ OrderUnitSpace.one_nonneg
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
  · exact (sub_le_self _ hδ1).trans (le_add_of_nonneg_right hδ1)
  · exact sub_le_iff_le_add.2 (hg.2 j)
  · exact hg.1 i
  · exact hab i j

/-- An approximate interpolant can be improved to any smaller error while moving by at most the sum
of the two errors. -/
lemma exists_isApproxInterpolant_near [Nontrivial F] {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 < δ')
    {g : F} (hg : IsApproxInterpolant a b δ g) :
    ∃ g', IsApproxInterpolant a b δ' g' ∧ g - (δ + δ') • 1 ≤ g' ∧ g' ≤ g + (δ + δ') • 1 := by
  obtain ⟨g', h₁, h₂⟩ :=
    hF.exists_approx_interpolant OrderUnitSpace.isOrderUnit_one (snoc_le_snoc hab hδ hg) hδ'
  refine ⟨g', ⟨fun i => by simpa using h₁ i.castSucc, fun j => by simpa using h₂ j.castSucc⟩,
    ?_, ?_⟩
  · have := h₁ (Fin.last n)
    rw [Fin.snoc_last] at this
    rw [add_smul, ← sub_sub]
    exact sub_le_iff_le_add.2 this
  · have := h₂ (Fin.last m)
    rw [Fin.snoc_last] at this
    rwa [add_smul, ← add_assoc]

/-- A sequence of interpolants with errors `(1 / 2) ^ k`, each within
`(1 / 2) ^ k + (1 / 2) ^ (k + 1)` of the next. -/
lemma exists_seq [Nontrivial F] [NeZero n] [NeZero m] : ∃ g : ℕ → F, ∀ k,
    IsApproxInterpolant a b ((1 / 2) ^ k) (g k) ∧
      g k - ((1 / 2) ^ k + (1 / 2) ^ (k + 1) : ℝ) • 1 ≤ g (k + 1) ∧
      g (k + 1) ≤ g k + ((1 / 2) ^ k + (1 / 2) ^ (k + 1) : ℝ) • 1 := by
  obtain ⟨g₀, hg₀⟩ := hF.exists_approx_interpolant OrderUnitSpace.isOrderUnit_one hab
    (by positivity : (0 : ℝ) < (1 / 2) ^ 0)
  have step (k : ℕ) (g : F) : ∃ g', IsApproxInterpolant a b ((1 / 2) ^ k) g →
      IsApproxInterpolant a b ((1 / 2) ^ (k + 1)) g' ∧
        g - ((1 / 2) ^ k + (1 / 2) ^ (k + 1) : ℝ) • 1 ≤ g' ∧
        g' ≤ g + ((1 / 2) ^ k + (1 / 2) ^ (k + 1) : ℝ) • 1 := by
    by_cases hg : IsApproxInterpolant a b ((1 / 2) ^ k) g
    · obtain ⟨g', hg'⟩ := hF.exists_isApproxInterpolant_near hab
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k)
        (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _) hg
      exact ⟨g', fun _ => hg'⟩
    · exact ⟨g, fun h => absurd h hg⟩
  choose next hnext using step
  let g : ℕ → F := fun k => Nat.rec g₀ (fun k g => next k g) k
  have hg (k : ℕ) : IsApproxInterpolant a b ((1 / 2) ^ k) (g k) := by
    induction k with
    | zero => exact hg₀
    | succ k ih => exact (hnext k (g k) ih).1
  exact ⟨g, fun k => ⟨hg k, (hnext k (g k) (hg k)).2⟩⟩

omit hF hab in
/-- A limit of interpolants with errors `(1 / 2) ^ k` is an exact interpolant. -/
lemma isApproxInterpolant_zero_of_tendsto {g : ℕ → F} {g' : F}
    (hg : ∀ k, IsApproxInterpolant a b ((1 / 2) ^ k) (g k)) (hlim : Tendsto g atTop (𝓝 g')) :
    (∀ i, a i ≤ g') ∧ ∀ j, g' ≤ b j := by
  have hpow {k l : ℕ} (hl : k ≤ l) : ((1 / 2 : ℝ) ^ l) • (1 : F) ≤ ((1 / 2 : ℝ) ^ k) • 1 :=
    smul_le_smul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hl)
      OrderUnitSpace.one_nonneg
  refine ⟨fun i => sub_nonpos.1 (le_zero_of_forall_le_half_pow fun k => ?_),
    fun j => sub_nonpos.1 (le_zero_of_forall_le_half_pow fun k => ?_)⟩
  · have := (isClosed_setOf_le (a i - ((1 / 2 : ℝ) ^ k) • 1)).mem_of_tendsto hlim <|
      eventually_atTop.2 ⟨k, fun l hl =>
        sub_le_iff_le_add.2 (((hg l).1 i).trans (add_le_add_right (hpow hl) _))⟩
    exact sub_le_comm.1 this
  · have := (isClosed_setOf_ge (b j + ((1 / 2 : ℝ) ^ k) • 1)).mem_of_tendsto hlim <|
      eventually_atTop.2 ⟨k, fun l hl => ((hg l).2 j).trans (add_le_add_right (hpow hl) _)⟩
    exact sub_le_iff_le_add'.2 this

/-- **Exact interpolation.** On a complete Archimedean order-unit space whose positive functionals
form a lattice, lower observables below upper observables have an interpolant. -/
lemma exists_interpolant [CompleteSpace F] [NeZero n] [NeZero m] :
    ∃ g : F, (∀ i, a i ≤ g) ∧ ∀ j, g ≤ b j := by
  rcases subsingleton_or_nontrivial F with hF1 | hF1
  · exact ⟨0, fun _ => (Subsingleton.elim _ _).le, fun _ => (Subsingleton.elim _ _).le⟩
  obtain ⟨g, hg⟩ := hF.exists_seq hab
  have hdist (k : ℕ) : dist (g k) (g (k + 1)) ≤ 4 / 2 / 2 ^ k :=
    (dist_le_of_le_of_le (by positivity) (hg k).2.1 (hg k).2.2).trans (by
      rw [pow_succ, one_div_pow]; field_simp; norm_num)
  obtain ⟨g', hg'⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hdist)
  exact ⟨g', isApproxInterpolant_zero_of_tendsto (fun k => (hg k).1) hg'⟩

end HasLatticeDualCone

namespace ProbabilisticTheory


open scoped ArchimedeanOrderUnitSpace in
/-- On a complete Archimedean order-unit space whose positive functionals form a lattice,
observables have the Riesz decomposition. -/
lemma _root_.HasLatticeDualCone.hasRieszDecomposition {F : Type*} [ArchimedeanOrderUnitSpace F]
    [CompleteSpace F] (hF : HasLatticeDualCone F) : HasRieszDecomposition F := by
  intro f₁ f₂ g hf₁ hf₂ hg
  obtain ⟨c, hlo, hhi⟩ := hF.exists_interpolant (a := ![0, g - f₂]) (b := ![g, f₁]) <| by
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨⟨hg.1, hf₁⟩, sub_le_self _ hf₂, sub_le_iff_le_add.2 hg.2⟩
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hlo hhi
  exact ⟨c, ⟨hlo.1, hhi.2⟩, sub_nonneg.2 hhi.1, sub_le_comm.1 hlo.2⟩

end ProbabilisticTheory
