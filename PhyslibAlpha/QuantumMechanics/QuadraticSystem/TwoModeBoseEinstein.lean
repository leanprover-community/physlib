/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.QuadraticSystem.BoseEinsteinDistribution
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!

# Bose–Einstein statistics for two independent bosonic modes

`BoseEinsteinDistribution.lean` proves the Bose–Einstein occupation-number formula for a single
harmonic-oscillator mode. Genuine statistical mechanics needs more than one mode at once: the
defining computational fact of an ideal Bose gas is that the *many-body* canonical ensemble of
several independent modes factorizes — the joint partition function is the *product* of the
single-mode partition functions, and each mode's occupation statistics are governed by its own
Bose–Einstein distribution, completely unaffected by the presence of the other modes. This file
proves that factorization for two modes (energies `ε₁, ε₂`, shared inverse temperature `β`), as
the base case of the general finitely-many-independent-modes statement.

## Main definitions

- `twoModePartitionFunction` : the joint canonical partition function `Z(β,ε₁,ε₂) = Σ_{n₁,n₂}
  exp(-β(ε₁n₁+ε₂n₂))` of two independent bosonic modes.
- `twoModePartitionFunction_hasSum` : it factorizes, `Z(β,ε₁,ε₂) = Z(β,ε₁)·Z(β,ε₂)`.
- `twoModeMeanOccupationFst_eq` : the first mode's mean occupation number, computed in the
  *joint* two-mode ensemble, is exactly its own single-mode Bose–Einstein distribution
  `1/(exp(βε₁)-1)` — independent of `ε₂`.

-/

@[expose] public section

namespace QuantumMechanics

noncomputable section

/-! ## A. The two-mode partition function factorizes -/

/-- The joint canonical partition function of two independent bosonic modes with energy quanta
`ε₁, ε₂` at shared inverse temperature `β`. -/
def twoModePartitionFunction (β ε₁ ε₂ : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, Real.exp (-(β * ε₁) * p.1 - (β * ε₂) * p.2)

theorem twoModeWeight_eq_mul (β ε₁ ε₂ : ℝ) (p : ℕ × ℕ) :
    Real.exp (-(β * ε₁) * p.1 - (β * ε₂) * p.2) =
      Real.exp (-(β * ε₁) * p.1) * Real.exp (-(β * ε₂) * p.2) := by
  rw [← Real.exp_add]; ring_nf

/-- **The joint partition function factorizes.** The two-mode Boltzmann sum is exactly the
product of the two single-mode partition functions — the defining fact that lets an ideal Bose
gas's many-body statistics be computed one mode at a time. -/
theorem twoModePartitionFunction_hasSum (β ε₁ ε₂ : ℝ) (hβ : 0 < β) (hε₁ : 0 < ε₁)
    (hε₂ : 0 < ε₂) :
    HasSum (fun p : ℕ × ℕ => Real.exp (-(β * ε₁) * p.1 - (β * ε₂) * p.2))
      (bosePartitionFunction β ε₁ * bosePartitionFunction β ε₂) := by
  have heq : (fun p : ℕ × ℕ => Real.exp (-(β * ε₁) * p.1 - (β * ε₂) * p.2)) =
      (fun p : ℕ × ℕ =>
        Real.exp (-(β * ε₁) * p.1) * Real.exp (-(β * ε₂) * p.2)) :=
    funext (twoModeWeight_eq_mul β ε₁ ε₂)
  rw [heq, bosePartitionFunction_eq β ε₁ hβ hε₁, bosePartitionFunction_eq β ε₂ hβ hε₂]
  have hf := bosePartitionFunction_hasSum β ε₁ hβ hε₁
  have hg := bosePartitionFunction_hasSum β ε₂ hβ hε₂
  have hprod : Summable (fun p : ℕ × ℕ =>
      Real.exp (-(β * ε₁) * (p.1:ℝ)) * Real.exp (-(β * ε₂) * (p.2:ℝ))) :=
    hf.summable.mul_of_nonneg hg.summable (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
  exact hf.mul hg hprod

theorem twoModePartitionFunction_eq (β ε₁ ε₂ : ℝ) (hβ : 0 < β) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    twoModePartitionFunction β ε₁ ε₂ = bosePartitionFunction β ε₁ * bosePartitionFunction β ε₂ :=
  (twoModePartitionFunction_hasSum β ε₁ ε₂ hβ hε₁ hε₂).tsum_eq

theorem twoModePartitionFunction_pos (β ε₁ ε₂ : ℝ) (hβ : 0 < β) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    0 < twoModePartitionFunction β ε₁ ε₂ := by
  rw [twoModePartitionFunction_eq β ε₁ ε₂ hβ hε₁ hε₂]
  exact mul_pos (bosePartitionFunction_pos β ε₁ hβ hε₁) (bosePartitionFunction_pos β ε₂ hβ hε₂)

/-! ## B. The mean occupation numbers factorize -/

/-- The first mode's mean occupation number, computed in the *joint* two-mode canonical
ensemble. -/
def twoModeMeanOccupationFst (β ε₁ ε₂ : ℝ) : ℝ :=
  (∑' p : ℕ × ℕ, (p.1 : ℝ) * Real.exp (-(β * ε₁) * p.1 - (β * ε₂) * p.2)) /
    twoModePartitionFunction β ε₁ ε₂

theorem twoModeMeanOccupationFstNumeratorHasSum (β ε₁ ε₂ : ℝ) (hβ : 0 < β) (hε₁ : 0 < ε₁)
    (hε₂ : 0 < ε₂) :
    HasSum (fun p : ℕ × ℕ => (p.1 : ℝ) * Real.exp (-(β * ε₁) * p.1 - (β * ε₂) * p.2))
      ((Real.exp (-(β * ε₁)) / (1 - Real.exp (-(β * ε₁))) ^ 2) * bosePartitionFunction β ε₂) := by
  have heq : (fun p : ℕ × ℕ => (p.1 : ℝ) * Real.exp (-(β * ε₁) * p.1 - (β * ε₂) * p.2)) =
      (fun p : ℕ × ℕ =>
        ((p.1 : ℝ) * Real.exp (-(β * ε₁) * p.1)) * Real.exp (-(β * ε₂) * p.2)) := by
    funext p
    rw [twoModeWeight_eq_mul β ε₁ ε₂ p]
    ring
  rw [heq, bosePartitionFunction_eq β ε₂ hβ hε₂]
  have hf := boseMeanOccupation_numerator_hasSum β ε₁ hβ hε₁
  have hg := bosePartitionFunction_hasSum β ε₂ hβ hε₂
  have hf_nonneg : ∀ n : ℕ, 0 ≤ (n : ℝ) * Real.exp (-(β * ε₁) * n) := fun n => by positivity
  have hprod : Summable (fun p : ℕ × ℕ =>
      ((p.1:ℝ) * Real.exp (-(β * ε₁) * (p.1:ℝ))) * Real.exp (-(β * ε₂) * (p.2:ℝ))) :=
    hf.summable.mul_of_nonneg hg.summable hf_nonneg (fun _ => (Real.exp_pos _).le)
  exact hf.mul hg hprod

/-- **The first mode's occupation statistics are unaffected by the second mode.** Computed in
the *joint* two-mode canonical ensemble, the first mode's mean occupation number is exactly its
own single-mode Bose–Einstein distribution `1/(exp(βε₁)-1)` — the second mode's energy `ε₂`
cancels out entirely. This is the concrete two-mode instance of the general fact that an ideal
Bose gas's per-mode statistics are computed independently, one mode at a time. -/
theorem twoModeMeanOccupationFstEq (β ε₁ ε₂ : ℝ) (hβ : 0 < β) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    twoModeMeanOccupationFst β ε₁ ε₂ = (Real.exp (β * ε₁) - 1)⁻¹ := by
  rw [twoModeMeanOccupationFst, (twoModeMeanOccupationFstNumeratorHasSum β ε₁ ε₂ hβ hε₁
    hε₂).tsum_eq, twoModePartitionFunction_eq β ε₁ ε₂ hβ hε₁ hε₂,
    mul_div_mul_right _ _ (bosePartitionFunction_pos β ε₂ hβ hε₂).ne',
    ← (boseMeanOccupation_numerator_hasSum β ε₁ hβ hε₁).tsum_eq]
  exact boseMeanOccupation_eq β ε₁ hβ hε₁

end

end QuantumMechanics
