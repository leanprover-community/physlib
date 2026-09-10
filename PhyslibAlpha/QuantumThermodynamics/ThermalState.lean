/-
Copyright (c) 2026 Huanhai Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanhai Zhou
-/
module

public import Physlib.Thermodynamics.Temperature.Basic
public import QuantumInfo.Entropy.Relative

/-!
# Quantum thermal states

This file defines the finite-dimensional quantum thermal (Gibbs) state associated with a
Hamiltonian. It provides both a real inverse-temperature parametrization and the physical
`Temperature` parametrization used by Physlib.

The main result is the Gibbs relative-entropy balance. It identifies an energy change from a
thermal state with the corresponding entropy change and quantum relative entropy.

## A. The partition function

## B. The thermal state

## C. The Gibbs relative-entropy balance
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace RealInnerProductSpace HermitianMat

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-!
## A. The partition function
-/

namespace HermitianMat

/-- The quantum partition function `Z(β) = tr(exp(-βH))` at real inverse temperature `β`. -/
noncomputable def partitionFunctionBetaReal (H : HermitianMat d ℂ) (β : ℝ) : ℝ :=
  ((-β) • H).exp.trace

/-- The finite-dimensional quantum partition function is strictly positive. -/
lemma partitionFunctionBetaReal_pos (H : HermitianMat d ℂ) (β : ℝ) :
    0 < H.partitionFunctionBetaReal β := by
  exact HermitianMat.trace_pos (((-β) • H).exp_pos)

end HermitianMat

/-!
## B. The thermal state
-/

namespace MState

/-- The thermal (Gibbs) state `exp(-βH) / Z(β)` at real inverse temperature `β`.

Unlike the classical `CanonicalEnsemble`, which is `Temperature`-primary, the
quantum side takes a real `β` as the primitive: the functional-calculus lemma
kit is stated most cleanly over `ℝ`, and real `β` keeps negative temperatures
reachable. `MState.thermal` is the `Temperature`-facing entry point matching
the classical idiom. -/
noncomputable def thermalBetaReal (H : HermitianMat d ℂ) (β : ℝ) : MState d where
  M := (H.partitionFunctionBetaReal β)⁻¹ • ((-β) • H).exp
  nonneg := smul_nonneg (inv_nonneg.mpr (H.partitionFunctionBetaReal_pos β).le)
    ((-β) • H).exp_nonneg
  tr := by
    rw [HermitianMat.trace_smul]
    change (H.partitionFunctionBetaReal β)⁻¹ * H.partitionFunctionBetaReal β = 1
    exact inv_mul_cancel₀ (H.partitionFunctionBetaReal_pos β).ne'

/-- The thermal state associated with a Hamiltonian at a physical `Temperature`. -/
noncomputable def thermal (H : HermitianMat d ℂ) (T : Temperature) : MState d :=
  thermalBetaReal H (T.β : ℝ)

/-- The matrix of a real-inverse-temperature thermal state is its normalized exponential. -/
lemma thermalBetaReal_M (H : HermitianMat d ℂ) (β : ℝ) :
    (thermalBetaReal H β).M =
      (H.partitionFunctionBetaReal β)⁻¹ • ((-β) • H).exp := rfl

/-- A real-inverse-temperature thermal state has trace one. -/
lemma thermalBetaReal_trace (H : HermitianMat d ℂ) (β : ℝ) :
    (thermalBetaReal H β).M.trace = 1 :=
  (thermalBetaReal H β).tr

/-- A finite-dimensional thermal state has full rank. -/
lemma thermalBetaReal_nonSingular (H : HermitianMat d ℂ) (β : ℝ) :
    (thermalBetaReal H β).M.NonSingular := by
  rw [thermalBetaReal_M]
  exact HermitianMat.nonSingular_smul
    (isUnit_iff_ne_zero.mpr
      (inv_ne_zero (H.partitionFunctionBetaReal_pos β).ne'))

/-- The density matrix of a finite-dimensional thermal state is positive definite. -/
lemma thermalBetaReal_posDef (H : HermitianMat d ℂ) (β : ℝ) :
    (thermalBetaReal H β).M.mat.PosDef := by
  exact (HermitianMat.nonSingular_iff_posDef_of_PSD (thermalBetaReal H β).nonneg).mp
    (thermalBetaReal_nonSingular H β)

/-- The physical-temperature thermal state is the real-`β` state at `Temperature.β`. -/
@[simp]
lemma thermal_eq_thermalBetaReal (H : HermitianMat d ℂ) (T : Temperature) :
    thermal H T = thermalBetaReal H (T.β : ℝ) := rfl

/-- The logarithm of a thermal state is `-βH - log Z(β)`. -/
lemma thermalBetaReal_log (H : HermitianMat d ℂ) (β : ℝ) :
    (thermalBetaReal H β).M.log =
      Real.log (H.partitionFunctionBetaReal β)⁻¹ • (1 : HermitianMat d ℂ) +
        (-β) • H := by
  rw [thermalBetaReal_M]
  rw [HermitianMat.log_smul
    (inv_ne_zero (H.partitionFunctionBetaReal_pos β).ne')]
  simp [HermitianMat.exp, HermitianMat.log, ← HermitianMat.cfc_comp]

/-!
## C. The Gibbs relative-entropy balance
-/

/-- For a thermal reference state, the energy change times `β` is the entropy change plus the
quantum relative entropy from the final state to the thermal state. -/
lemma gibbsRelativeEntropyBalanceBetaReal (ρ : MState d) (H : HermitianMat d ℂ) (β : ℝ) :
    β * (ρ.exp_val H - (thermalBetaReal H β).exp_val H) =
      Sᵥₙ ρ - Sᵥₙ (thermalBetaReal H β) +
        (qRelativeEnt ρ (thermalBetaReal H β)).toReal := by
  let γ := thermalBetaReal H β
  haveI : γ.M.NonSingular := thermalBetaReal_nonSingular H β
  have hLogExpVal (σ : MState d) :
      ⟪σ.M, γ.M.log⟫ =
        Real.log (H.partitionFunctionBetaReal β)⁻¹ + (-β) * σ.exp_val H := by
    rw [show γ.M.log =
      Real.log (H.partitionFunctionBetaReal β)⁻¹ • (1 : HermitianMat d ℂ) +
        (-β) • H by exact thermalBetaReal_log H β]
    simp [MState.exp_val, inner_add_right, HermitianMat.inner_smul_right,
      HermitianMat.inner_one, σ.tr, mul_comm]
  have hRelativeEntropyExpand :
      (qRelativeEnt ρ γ).toReal = -Sᵥₙ ρ - ⟪ρ.M, γ.M.log⟫ := by
    have h := congrArg EReal.toReal (qRelativeEnt_eq_neg_Sᵥₙ_add ρ γ)
    simp only [HermitianMat.nonSingular_ker_bot, bot_le, if_true] at h
    rw [EReal.toReal_add (by simp) (by simp) (by simp) (by simp)] at h
    simpa [sub_eq_add_neg, EReal.toReal_coe_ennreal] using h
  have hThermalEntropy :
      Sᵥₙ γ =
        -(Real.log (H.partitionFunctionBetaReal β)⁻¹ +
          (-β) * γ.exp_val H) := by
    rw [Sᵥₙ_eq_neg_trace_log]
    rw [real_inner_comm]
    rw [hLogExpVal γ]
  change β * (ρ.exp_val H - γ.exp_val H) =
    Sᵥₙ ρ - Sᵥₙ γ + (qRelativeEnt ρ γ).toReal
  rw [hRelativeEntropyExpand, hThermalEntropy, hLogExpVal ρ]
  ring

/-- Temperature-parametrized form of the Gibbs relative-entropy balance. -/
lemma gibbsRelativeEntropyBalance (ρ : MState d) (H : HermitianMat d ℂ) (T : Temperature) :
    (T.β : ℝ) * (ρ.exp_val H - (thermal H T).exp_val H) =
      Sᵥₙ ρ - Sᵥₙ (thermal H T) + (qRelativeEnt ρ (thermal H T)).toReal := by
  exact gibbsRelativeEntropyBalanceBetaReal ρ H (T.β : ℝ)

end MState
